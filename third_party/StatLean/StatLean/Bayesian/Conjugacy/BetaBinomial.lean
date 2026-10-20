module
public import StatLean.Bayesian.Conjugacy.Defs
public import StatLean.Bayesian.Conjugacy.Criterion
public import Mathlib.Probability.Distributions.Beta

@[expose] public section

/-!
# Beta-Binomial conjugacy

The classical first example of Bayes' theorem: for a success probability `θ ~ Beta(α, β)` and one
binomial observation `k ~ ℬ(n, θ)`,

* **posterior** (Gelman §2.4): `θ | k ~ Beta(α + k, β + n − k)`;
* **marginal** (the Beta-Binomial pmf, Gelman §2.4):
  `P(k) = C(n, k) · B(α + k, β + n − k) / B(α, β)`.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §2.4
(binomial model), p. 34.

**Proof formalization notes.** One pointwise pdf-algebra lemma (`betaPDF_mul_clampPow`: Beta pdf ×
clamped power = Beta-function ratio × updated Beta pdf, using `Real.rpow_natCast`/`rpow_add` on
`(0,1)` where the clamp is the identity, and `ProbabilityTheory.beta` in Γ-form) feeds the
conjugacy criterion; the data space `Fin (n+1)` is finite discrete, and the binomial kernel's
Markov property is the binomial theorem `add_pow` at `clamp θ + (1 − clamp θ) = 1`. Off `(0, 1)`
both sides of the algebra vanish (the Beta pdf is zero), which is why clamping is harmless.

**Bibliographic comments.** This is the original Bayesian computation: Bayes's 1763 essay treats
exactly the uniform-prior case `Beta(1,1)`, and Laplace's rule of
succession builds on it (`Conjugacy.BetaBernoulli`). The modern conjugate-family reading is
Raiffa–Schlaifer (1961); Diaconis and Ylvisaker (1985, "Quantifying prior opinion") use the
spinning-coin Beta-Binomial as the canonical worked example.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- `unitClamp` is measurable (it is continuous: `max 0 (min 1 ·)`). -/
private theorem measurable_unitClamp : Measurable unitClamp :=
  (continuous_const.max (continuous_const.min continuous_id)).measurable

/-- Joint measurability of the binomial density `(θ, k) ↦ C(n,k) clamp^k (1−clamp)^(n−k)`
(the data space `Fin (n+1)` is finite discrete). -/
private theorem measurable_uncurry_binomialDensity (n : ℕ) :
    Measurable (Function.uncurry (binomialDensity n)) := by
  refine measurable_from_prod_countable_left (fun k => ?_)
  simp only [Function.uncurry, binomialDensity]
  exact ((measurable_const.mul (measurable_unitClamp.pow_const _)).mul
    ((measurable_const.sub measurable_unitClamp).pow_const _)).ennreal_ofReal

/-- The binomial kernel is Markov for every real parameter (clamping; binomial theorem). -/
instance (n : ℕ) : IsMarkovKernel (binomialKernel n) := by
  refine ⟨fun θ => ?_⟩
  rw [binomialKernel, Kernel.withDensity_apply _ (measurable_uncurry_binomialDensity n),
    Kernel.const_apply]
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, lintegral_count, tsum_fintype]
  have hc0 : (0:ℝ) ≤ unitClamp θ := le_max_left _ _
  have hc1 : unitClamp θ ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have h1c : (0:ℝ) ≤ 1 - unitClamp θ := by linarith
  simp only [binomialDensity]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc0 _)) (pow_nonneg h1c _))]
  have hbin : ∑ k : Fin (n + 1),
      (n.choose (k : ℕ) : ℝ) * unitClamp θ ^ (k : ℕ) * (1 - unitClamp θ) ^ (n - (k : ℕ)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range fun k =>
      (n.choose k : ℝ) * unitClamp θ ^ k * (1 - unitClamp θ) ^ (n - k)]
    have hsum1 : unitClamp θ + (1 - unitClamp θ) = 1 := by ring
    calc ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * unitClamp θ ^ k * (1 - unitClamp θ) ^ (n - k)
        = ∑ k ∈ Finset.range (n + 1),
            unitClamp θ ^ k * (1 - unitClamp θ) ^ (n - k) * (n.choose k : ℝ) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = (unitClamp θ + (1 - unitClamp θ)) ^ n := (add_pow _ _ _).symm
      _ = 1 := by rw [hsum1, one_pow]
  rw [hbin, ENNReal.ofReal_one]

/-- Pointwise pdf algebra: Beta pdf times a clamped-power factor is a Beta-function ratio times
the updated Beta pdf. Both sides vanish off `(0, 1)`. -/
theorem betaPDF_mul_clampPow {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Gelman §2.4
    (hα : 0 < α) (hβ : 0 < β) (a b : ℕ) (θ : ℝ) :
    betaPDF α β θ * ENNReal.ofReal (unitClamp θ ^ a * (1 - unitClamp θ) ^ b)
      = ENNReal.ofReal (ProbabilityTheory.beta (α + a) (β + b) / ProbabilityTheory.beta α β)
          * betaPDF (α + a) (β + b) θ := by
  by_cases hθ : 0 < θ ∧ θ < 1
  · obtain ⟨h0, h1⟩ := hθ
    have h1c : (0:ℝ) < 1 - θ := by linarith
    have hc : unitClamp θ = θ := by
      simp only [unitClamp]; rw [min_eq_right h1.le, max_eq_right h0.le]
    have hα' : (0:ℝ) < α + (a : ℝ) := add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg a)
    have hβ' : (0:ℝ) < β + (b : ℝ) := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg b)
    have hbpos : (0:ℝ) < beta α β := beta_pos hα hβ
    have hbα : beta α β ≠ 0 := hbpos.ne'
    have hbα' : beta (α + a) (β + b) ≠ 0 := (beta_pos hα' hβ').ne'
    have hnn1 : (0:ℝ) ≤ 1 / beta α β * θ ^ (α - 1) * (1 - θ) ^ (β - 1) :=
      mul_nonneg (mul_nonneg (one_div_pos.mpr hbpos).le (Real.rpow_pos_of_pos h0 _).le)
        (Real.rpow_pos_of_pos h1c _).le
    rw [hc, betaPDF_of_pos_lt_one h0 h1, betaPDF_of_pos_lt_one h0 h1,
      ← ENNReal.ofReal_mul hnn1,
      ← ENNReal.ofReal_mul (div_pos (beta_pos hα' hβ') hbpos).le]
    congr 1
    have e1 : θ ^ (α - 1) * θ ^ a = θ ^ (α + (a : ℝ) - 1) := by
      rw [← Real.rpow_natCast θ a, ← Real.rpow_add h0]; congr 1; ring
    have e2 : (1 - θ) ^ (β - 1) * (1 - θ) ^ b = (1 - θ) ^ (β + (b : ℝ) - 1) := by
      rw [← Real.rpow_natCast (1 - θ) b, ← Real.rpow_add h1c]; congr 1; ring
    rw [show (1 / beta α β * θ ^ (α - 1) * (1 - θ) ^ (β - 1)) * (θ ^ a * (1 - θ) ^ b)
          = 1 / beta α β * (θ ^ (α - 1) * θ ^ a) * ((1 - θ) ^ (β - 1) * (1 - θ) ^ b) by ring,
      e1, e2]
    field_simp
  · have hz1 : betaPDF α β θ = 0 := by
      rcases not_and_or.mp hθ with h | h
      · exact betaPDF_eq_zero_of_nonpos (not_lt.mp h)
      · exact betaPDF_eq_zero_of_one_le (not_lt.mp h)
    have hz2 : betaPDF (α + a) (β + b) θ = 0 := by
      rcases not_and_or.mp hθ with h | h
      · exact betaPDF_eq_zero_of_nonpos (not_lt.mp h)
      · exact betaPDF_eq_zero_of_one_le (not_lt.mp h)
    rw [hz1, hz2, zero_mul, mul_zero]

/-- **Beta-Binomial posterior** (Gelman §2.4): observing `k` successes in
`n` trials updates `Beta(α, β)` to `Beta(α + k, β + (n − k))`, predictive-a.e. -/
theorem beta_binomial_posterior_ae {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Gelman §2.4
    (hα : 0 < α) (hβ : 0 < β)
    -- LEAN-ONLY: instance plumbing, derivable from hα/hβ via `isProbabilityMeasureBeta`
    [IsFiniteMeasure (betaMeasure α β)] (n : ℕ) :
    ∀ᵐ k ∂(binomialKernel n ∘ₘ betaMeasure α β),
      ((binomialKernel n)†(betaMeasure α β)) k
        = betaMeasure (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) := by
  have hbeta : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  refine posterior_ae_eq_of_withDensity_eq_smul
    (ν := Measure.count) (p := binomialDensity n)
    (ρ := fun k => betaMeasure (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)))
    (c := fun k => ENNReal.ofReal ((n.choose (k : ℕ) : ℝ)
      * (beta (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) / beta α β)))
    (measurable_uncurry_binomialDensity n) ?_ ?_ ?_
  · intro θ
    rw [binomialKernel, Kernel.withDensity_apply _ (measurable_uncurry_binomialDensity n),
      Kernel.const_apply]
  · intro k
    exact isProbabilityMeasureBeta (add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg _))
      (add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg _))
  · intro k
    have hg : Measurable (fun θ => binomialDensity n θ k) :=
      (measurable_uncurry_binomialDensity n).of_uncurry_right
    have hck : ENNReal.ofReal ((n.choose (k : ℕ) : ℝ)
        * (beta (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) / beta α β)) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hdens : betaPDF α β * (fun θ => binomialDensity n θ k)
        = (ENNReal.ofReal ((n.choose (k : ℕ) : ℝ)
            * (beta (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) / beta α β)))
          • betaPDF (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) := by
      funext θ
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, binomialDensity]
      rw [show (n.choose (k : ℕ) : ℝ) * unitClamp θ ^ (k : ℕ) * (1 - unitClamp θ) ^ (n - (k : ℕ))
            = (n.choose (k : ℕ) : ℝ)
              * (unitClamp θ ^ (k : ℕ) * (1 - unitClamp θ) ^ (n - (k : ℕ))) from by ring,
        ENNReal.ofReal_mul (by positivity), mul_left_comm,
        betaPDF_mul_clampPow hα hβ (k : ℕ) (n - (k : ℕ)) θ, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
    simp only [betaMeasure]
    rw [← withDensity_mul _ hbeta hg, hdens, withDensity_smul' _ _ hck]

/-- **Beta-Binomial marginal** (Gelman §2.4): the prior predictive pmf is
`C(n,k) · B(α+k, β+n−k) / B(α, β)`. -/
theorem beta_binomial_predictiveDensity {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Gelman §2.4
    (hα : 0 < α) (hβ : 0 < β) (n : ℕ) (k : Fin (n + 1)) :
    predictiveDensity (binomialDensity n) (betaMeasure α β) k
      = ENNReal.ofReal ((n.choose k : ℝ)
          * ProbabilityTheory.beta (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ))
          / ProbabilityTheory.beta α β) := by
  have hbeta : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  have hbeta' : Measurable (betaPDF (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ))) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  have hg : Measurable (fun θ => binomialDensity n θ k) :=
    (measurable_uncurry_binomialDensity n).of_uncurry_right
  have hα' : (0:ℝ) < α + (k : ℕ) := add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg _)
  have hβ' : (0:ℝ) < β + ((n - (k : ℕ) : ℕ) : ℝ) :=
    add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg _)
  have hdens : ∀ θ, betaPDF α β θ * binomialDensity n θ k
      = ENNReal.ofReal ((n.choose (k : ℕ) : ℝ)
          * (beta (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) / beta α β))
        * betaPDF (α + (k : ℕ)) (β + ((n - (k : ℕ) : ℕ) : ℝ)) θ := by
    intro θ
    simp only [binomialDensity]
    rw [show (n.choose (k : ℕ) : ℝ) * unitClamp θ ^ (k : ℕ) * (1 - unitClamp θ) ^ (n - (k : ℕ))
          = (n.choose (k : ℕ) : ℝ)
            * (unitClamp θ ^ (k : ℕ) * (1 - unitClamp θ) ^ (n - (k : ℕ))) from by ring,
      ENNReal.ofReal_mul (by positivity), mul_left_comm,
      betaPDF_mul_clampPow hα hβ (k : ℕ) (n - (k : ℕ)) θ, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
  simp only [predictiveDensity, betaMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul _ hbeta hg]
  simp only [Pi.mul_apply]
  rw [lintegral_congr hdens, lintegral_const_mul _ hbeta', lintegral_betaPDF_eq_one hα' hβ',
    mul_one, mul_div_assoc]

end StatLean.Bayesian
