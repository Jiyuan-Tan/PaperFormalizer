module
public import StatLean.Bayesian.Conjugacy.Defs
public import StatLean.Bayesian.Conjugacy.Criterion
public import StatLean.Bayesian.ForMathlib.IIDKernel
public import Mathlib.Probability.Distributions.Gamma

@[expose] public section

/-!
# Gamma-Poisson conjugacy

For a Poisson rate `λ ~ Gamma(a, r)` (shape `a`, rate `r`) and iid counts
`y₁, …, yₙ ~ Poisson(λ)`:
$$\lambda \mid y_{1:n} \sim \mathrm{Gamma}\Big(a + \sum_i y_i,\ r + n\Big)
  \qquad \text{predictive-a.e.}$$

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §2.6
(Poisson model), p. 42.

**Proof formalization notes.** The pinned `gammaMeasure a r` is shape/RATE, exactly matching
Gelman's `𝒢(α, β)` with `β` a rate, so the update reads `Gamma(a + S, r + n)` with no
reparameterization. The rate clamp `Real.toNNReal` is invisible under the Gamma prior (its pdf
vanishes on `θ ≤ 0`); the Poisson kernel is Markov for every real parameter since
`poissonPMFReal` sums to `1` at every `ℝ≥0` rate (pinned `poissonPMFRealSum`; at rate `0` the law
is the Dirac mass at `0`). Pointwise algebra: `gammaPDF a r θ · ∏ᵢ e^{−θ}θ^{yᵢ}/yᵢ! =
C(y) · gammaPDF (a + Σyᵢ) (r + n) θ` on `θ > 0` (`Real.rpow_natCast`, `rpow_add`,
`Real.exp_add`), fed to the criterion via `iidKernel_withDensity`.

**Bibliographic comments.** The Gamma prior for Poisson intensities is the count-data workhorse
of Bayesian practice, from actuarial credibility theory (Bühlmann 1967) to empirical-Bayes
shrinkage of rates (Robbins 1956; Efron–Morris 1975 in the Gaussian analogue). It is one of the
Raiffa–Schlaifer (1961) natural conjugate pairs; the negative-binomial marginal it induces is the
classical overdispersed count model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- Joint measurability of the Poisson density `(θ, k) ↦ ofReal (poissonPMFReal θ⁺ k)`. -/
private theorem measurable_uncurry_poissonDensity :
    Measurable (Function.uncurry poissonDensity) := by
  refine measurable_from_prod_countable_left (fun k => ?_)
  change Measurable fun θ : ℝ => poissonDensity θ k
  unfold poissonDensity
  refine Measurable.ennreal_ofReal ?_
  have hr : Measurable fun r : ℝ≥0 => poissonPMFReal r k := by
    unfold poissonPMFReal; fun_prop
  exact hr.comp measurable_real_toNNReal

/-- The Poisson kernel is Markov for every real parameter (rate clamped at `0`). -/
instance : IsMarkovKernel poissonKernel := by
  refine ⟨fun θ => ⟨?_⟩⟩
  rw [poissonKernel, Kernel.withDensity_apply _ measurable_uncurry_poissonDensity,
    Kernel.const_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_count]
  simp only [poissonDensity]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => poissonPMFReal_nonneg)
      (poissonPMFRealSum _).summable,
    show ∑' n, poissonPMFReal θ.toNNReal n = 1 from (poissonPMFRealSum _).tsum_eq,
    ENNReal.ofReal_one]

/-- Pointwise pdf algebra: Gamma pdf times an iid Poisson likelihood is an explicit constant times
the updated Gamma pdf; both sides vanish on `θ ≤ 0`. -/
theorem gammaPDF_mul_prod_poissonDensity {a r : ℝ}
    -- USER-INPUT: positive Gamma shape and rate; Gelman §2.6
    (ha : 0 < a) (hr : 0 < r) {n : ℕ} (y : Fin n → ℕ) (θ : ℝ) :
    gammaPDF a r θ * ∏ i, poissonDensity θ (y i)
      = ENNReal.ofReal
          ((r ^ a * Real.Gamma (a + ∑ i, (y i : ℝ)))
            / (Real.Gamma a * (r + n) ^ (a + ∑ i, (y i : ℝ)) * ∏ i, (Nat.factorial (y i) : ℝ)))
          * gammaPDF (a + ∑ i, (y i : ℝ)) (r + n) θ := by
  rcases lt_or_ge θ 0 with hlt | hθ0
  · -- both sides vanish for `θ < 0`
    simp only [gammaPDF_of_neg hlt, zero_mul, mul_zero]
  · -- `0 ≤ θ`: pointwise real algebra
    have hGa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
    have hSnn : (0 : ℝ) ≤ ∑ i, (y i : ℝ) := Finset.sum_nonneg (fun i _ => by positivity)
    have hGaS : (0 : ℝ) < Real.Gamma (a + ∑ i, (y i : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
    have hrnpos : (0 : ℝ) < r + n := add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg n)
    have hrn : (0 : ℝ) < (r + n) ^ (a + ∑ i, (y i : ℝ)) := Real.rpow_pos_of_pos hrnpos _
    have hfac : (0 : ℝ) < ∏ i, (Nat.factorial (y i) : ℝ) :=
      Finset.prod_pos (fun i _ => by positivity)
    have hC : (0 : ℝ) ≤ (r ^ a * Real.Gamma (a + ∑ i, (y i : ℝ)))
        / (Real.Gamma a * (r + n) ^ (a + ∑ i, (y i : ℝ)) * ∏ i, (Nat.factorial (y i) : ℝ)) :=
      div_nonneg (mul_nonneg (Real.rpow_nonneg hr.le a) hGaS.le)
        (mul_nonneg (mul_nonneg hGa.le hrn.le) hfac.le)
    have hga0 : 0 ≤ gammaPDFReal a r θ := by
      rw [gammaPDFReal, if_pos hθ0]
      exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hr.le a) hGa.le)
        (Real.rpow_nonneg hθ0 _)) (Real.exp_pos _).le
    have hθtoN : ((θ.toNNReal : ℝ)) = θ := Real.coe_toNNReal θ hθ0
    have hcast : ((∑ i, y i : ℕ) : ℝ) = ∑ i, (y i : ℝ) := by push_cast; rfl
    have hexp : Real.exp (-(r * θ)) * Real.exp (-θ) ^ n = Real.exp (-((r + n) * θ)) := by
      rw [← Real.exp_nsmul, nsmul_eq_mul, ← Real.exp_add]
      congr 1; ring
    have hpow : θ ^ (a - 1) * θ ^ (∑ i, y i) = θ ^ ((a + ∑ i, (y i : ℝ)) - 1) := by
      rcases eq_or_lt_of_le hθ0 with h0 | hpos
      · rcases Nat.eq_zero_or_pos (∑ i, y i) with hs | hs
        · rw [hs, pow_zero, mul_one]
          congr 1
          rw [← hcast, hs]; push_cast; ring
        · rw [← h0, zero_pow hs.ne', mul_zero, eq_comm]
          apply Real.zero_rpow
          have h1 : (1 : ℝ) ≤ ∑ i, (y i : ℝ) := by rw [← hcast]; exact_mod_cast hs
          nlinarith [ha]
      · rw [← Real.rpow_natCast θ (∑ i, y i), ← Real.rpow_add hpos, hcast]
        congr 1; ring
    simp only [gammaPDF, poissonDensity]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => poissonPMFReal_nonneg),
      ← ENNReal.ofReal_mul hga0, ← ENNReal.ofReal_mul hC]
    congr 1
    simp only [gammaPDFReal, if_pos hθ0, poissonPMFReal, hθtoN]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum, ← hpow, ← hexp]
    field_simp

set_option maxHeartbeats 1000000 in
/-- **Gamma-Poisson posterior** (Gelman §2.6, `n`-sample form): iid Poisson counts update
`Gamma(a, r)` to `Gamma(a + ∑ yᵢ, r + n)`, predictive-a.e. -/
theorem gamma_poisson_posterior_ae {a r : ℝ}
    -- USER-INPUT: positive Gamma shape and rate; Gelman §2.6
    (ha : 0 < a) (hr : 0 < r)
    -- LEAN-ONLY: instance plumbing, derivable from ha/hr via `isProbabilityMeasure_gammaMeasure`
    [IsFiniteMeasure (gammaMeasure a r)] (n : ℕ) :
    ∀ᵐ y ∂(iidKernel poissonKernel n ∘ₘ gammaMeasure a r),
      ((iidKernel poissonKernel n)†(gammaMeasure a r)) y
        = gammaMeasure (a + ∑ i, (y i : ℝ)) (r + n) := by
  have hunc : Measurable (Function.uncurry poissonDensity) := measurable_uncurry_poissonDensity
  have hκ : ∀ θ, poissonKernel θ = Measure.count.withDensity (poissonDensity θ) := by
    intro θ
    rw [poissonKernel, Kernel.withDensity_apply _ hunc, Kernel.const_apply]
  refine posterior_ae_eq_of_withDensity_eq_smul
    (ν := Measure.pi fun _ : Fin n => (Measure.count : Measure ℕ))
    (p := fun θ (y : Fin n → ℕ) => ∏ i, poissonDensity θ (y i))
    (ρ := fun y => gammaMeasure (a + ∑ i, (y i : ℝ)) (r + n))
    (c := fun y => ENNReal.ofReal
      ((r ^ a * Real.Gamma (a + ∑ i, (y i : ℝ)))
        / (Real.Gamma a * (r + n) ^ (a + ∑ i, (y i : ℝ)) * ∏ i, (Nat.factorial (y i) : ℝ))))
    (measurable_uncurry_prod_likelihood hunc)
    (fun θ => iidKernel_withDensity hunc hκ n θ)
    (fun y => isProbabilityMeasure_gammaMeasure
      (by have : (0 : ℝ) ≤ ∑ i, (y i : ℝ) := Finset.sum_nonneg (fun i _ => by positivity); linarith)
      (add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg n)))
    ?_
  intro y
  have hprior : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hprod : Measurable (fun θ => ∏ i, poissonDensity θ (y i)) :=
    Finset.measurable_prod _ (fun i _ => hunc.comp (measurable_id.prodMk measurable_const))
  have hfun : (gammaPDF a r) * (fun θ => ∏ i, poissonDensity θ (y i))
      = ENNReal.ofReal
          ((r ^ a * Real.Gamma (a + ∑ i, (y i : ℝ)))
            / (Real.Gamma a * (r + n) ^ (a + ∑ i, (y i : ℝ)) * ∏ i, (Nat.factorial (y i) : ℝ)))
        • (fun θ => gammaPDF (a + ∑ i, (y i : ℝ)) (r + n) θ) := by
    funext θ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact gammaPDF_mul_prod_poissonDensity ha hr y θ
  simp only [gammaMeasure]
  rw [← withDensity_mul _ hprior hprod, hfun, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

end StatLean.Bayesian
