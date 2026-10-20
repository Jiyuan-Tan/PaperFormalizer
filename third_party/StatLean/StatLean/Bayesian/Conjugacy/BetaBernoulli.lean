module
public import StatLean.Bayesian.Conjugacy.BetaBinomial
public import StatLean.Bayesian.ForMathlib.IIDKernel
public import StatLean.Bayesian.Updating.Defs

@[expose] public section

/-!
# Beta-Bernoulli conjugacy and Laplace's rule of succession

For iid Bernoulli data with a Beta prior on the success probability:

* **posterior**: after `n` tosses with `s = successes y`,
  `θ | y ~ Beta(α + s, β + (n − s))`;
* **posterior mean of the success probability** (`lintegral_unitClamp_betaMeasure`):
  `E[θ] = α/(α + β)` under `Beta(α, β)`;
* **Laplace's rule of succession** (Gelman §2.4's historical example, formalized via the posterior
  predictive): the predictive probability of a further success is
  $$P(y_{n+1} = 1 \mid y_{1:n}) = \frac{\alpha + s}{\alpha + \beta + n}.$$

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §2.1 and
§2.4 (binomial with conjugate Beta prior), pp. 29, 34.

**Proof formalization notes.** The iid Bernoulli likelihood is a clamped-power factor with
exponents `successes y` and `n − successes y` (`Bool.toNat` bookkeeping), so the posterior is the
Beta-Binomial algebra (`betaPDF_mul_clampPow`) fed to the criterion via `iidKernel_withDensity`.
The succession rule composes the posterior with one more Bernoulli through `posteriorPredictive`
and evaluates `{true}` by the Beta-mean lemma, itself proved by the pdf-ratio trick
(`betaPDF_mul_clampPow` with exponents `(1, 0)` + `lintegral_betaPDF_eq_one` + `Real.Gamma_add_one`
for the Beta-function ratio `B(α+1,β)/B(α,β) = α/(α+β)`).

**Bibliographic comments.** The rule of succession is P. S. Laplace's ("Mémoire sur la
probabilité des causes par les événements," 1774): after the sun has risen `n` times, the odds it
rises again are `(n+1)/(n+2)` — the case `α = β = 1`, `s = n`. It is the first posterior
predictive computation in history and the standard smoothing device ("add-one" or Laplace
smoothing) in modern categorical modeling. De Finetti's representation theorem explains why
exchangeable binary data reduce to exactly this model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- `unitClamp` is measurable (continuous: `max 0 (min 1 ·)`). -/
private theorem measurable_unitClamp : Measurable unitClamp :=
  (continuous_const.max (continuous_const.min continuous_id)).measurable

/-- Joint measurability of the Bernoulli density. -/
private theorem measurable_uncurry_bernoulliDensity :
    Measurable (Function.uncurry bernoulliDensity) := by
  refine measurable_from_prod_countable_left (fun b => ?_)
  simp only [Function.uncurry, bernoulliDensity]
  cases b
  · simpa using (measurable_const.sub measurable_unitClamp).ennreal_ofReal
  · simpa using measurable_unitClamp.ennreal_ofReal

/-- The Bernoulli kernel is Markov for every real parameter (clamping). -/
instance : IsMarkovKernel bernoulliKernel := by
  refine ⟨fun θ => ?_⟩
  rw [bernoulliKernel, Kernel.withDensity_apply _ measurable_uncurry_bernoulliDensity,
    Kernel.const_apply]
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, lintegral_count, tsum_fintype,
    Fintype.sum_bool]
  have hc0 : (0:ℝ) ≤ unitClamp θ := le_max_left _ _
  have hc1 : unitClamp θ ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have ht : bernoulliDensity θ true = ENNReal.ofReal (unitClamp θ) := by simp [bernoulliDensity]
  have hf : bernoulliDensity θ false = ENNReal.ofReal (1 - unitClamp θ) := by simp [bernoulliDensity]
  rw [ht, hf, ← ENNReal.ofReal_add hc0 (by linarith),
    show unitClamp θ + (1 - unitClamp θ) = 1 from by ring, ENNReal.ofReal_one]

/-- **Posterior mean of a clamped success probability under a Beta law**: `α/(α+β)` (Gelman §2.4 with `n = 1`, `x = 1`; the pdf-ratio trick). -/
theorem lintegral_unitClamp_betaMeasure {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Gelman §2.4
    (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ θ, ENNReal.ofReal (unitClamp θ) ∂betaMeasure α β
      = ENNReal.ofReal (α / (α + β)) := by
  have hbeta : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  have hbeta1 : Measurable (betaPDF (α + 1) β) := (measurable_betaPDFReal _ _).ennreal_ofReal
  have hratio : beta (α + 1) β / beta α β = α / (α + β) := by
    have hga : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
    have hgb : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
    have hgab : Real.Gamma (α + β) ≠ 0 := (Real.Gamma_pos_of_pos (add_pos hα hβ)).ne'
    have hab : α + β ≠ 0 := (add_pos hα hβ).ne'
    simp only [ProbabilityTheory.beta, show α + 1 + β = α + β + 1 from by ring,
      Real.Gamma_add_one (add_pos hα hβ).ne', Real.Gamma_add_one hα.ne']
    field_simp
  have key : ∀ θ, betaPDF α β θ * ENNReal.ofReal (unitClamp θ)
      = ENNReal.ofReal (beta (α + 1) β / beta α β) * betaPDF (α + 1) β θ := by
    intro θ
    have hh := betaPDF_mul_clampPow hα hβ 1 0 θ
    simp only [Nat.cast_one, Nat.cast_zero, add_zero, pow_one, pow_zero, mul_one] at hh
    exact hh
  simp only [betaMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul _ hbeta measurable_unitClamp.ennreal_ofReal]
  simp only [Pi.mul_apply]
  rw [lintegral_congr key, lintegral_const_mul _ hbeta1,
    lintegral_betaPDF_eq_one (by linarith) hβ, mul_one, hratio]

/-- The iid Bernoulli likelihood is the clamped-power factor with exponents `successes y` and
`n − successes y`. -/
private theorem prod_bernoulliDensity {n : ℕ} (θ : ℝ) (y : Fin n → Bool) :
    ∏ i, bernoulliDensity θ (y i)
      = ENNReal.ofReal (unitClamp θ ^ successes y * (1 - unitClamp θ) ^ (n - successes y)) := by
  have hc0 : (0:ℝ) ≤ unitClamp θ := le_max_left _ _
  have h1c : (0:ℝ) ≤ 1 - unitClamp θ := by
    have : unitClamp θ ≤ 1 := max_le zero_le_one (min_le_left _ _); linarith
  have hn : ∑ i, ((1 - (y i).toNat) + (y i).toNat) = n := by
    have hone : ∀ i, (1 - (y i).toNat) + (y i).toNat = 1 := fun i => by cases y i <;> rfl
    simp [hone]
  have hadd : ∑ i, (1 - (y i).toNat) + successes y = n := by
    rw [successes, ← Finset.sum_add_distrib]; exact hn
  have hsum : ∑ i, (1 - (y i).toNat) = n - successes y := Nat.eq_sub_of_add_eq hadd
  have hfac : ∀ i, (if y i then unitClamp θ else 1 - unitClamp θ)
      = unitClamp θ ^ (y i).toNat * (1 - unitClamp θ) ^ (1 - (y i).toNat) := by
    intro i; cases y i <;> simp
  simp only [bernoulliDensity]
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => by cases y i <;> first | exact hc0 | exact h1c)]
  congr 1
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hsum]
  rfl

/-- **Beta-Bernoulli posterior** (iid sample): `θ | y ~ Beta(α + s, β + (n − s))` with
`s = successes y`, predictive-a.e. -/
theorem beta_bernoulli_posterior_ae {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Gelman §2.4
    (hα : 0 < α) (hβ : 0 < β)
    -- LEAN-ONLY: instance plumbing, derivable from hα/hβ via `isProbabilityMeasureBeta`
    [IsFiniteMeasure (betaMeasure α β)] (n : ℕ) :
    ∀ᵐ y ∂(iidKernel bernoulliKernel n ∘ₘ betaMeasure α β),
      ((iidKernel bernoulliKernel n)†(betaMeasure α β)) y
        = betaMeasure (α + successes y) (β + ((n - successes y : ℕ) : ℝ)) := by
  have hbeta : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  have hbern : ∀ θ, bernoulliKernel θ = Measure.count.withDensity (bernoulliDensity θ) :=
    fun θ => by rw [bernoulliKernel,
      Kernel.withDensity_apply _ measurable_uncurry_bernoulliDensity, Kernel.const_apply]
  refine posterior_ae_eq_of_withDensity_eq_smul
    (ν := Measure.pi fun _ : Fin n => Measure.count)
    (p := fun θ y => ∏ i, bernoulliDensity θ (y i))
    (ρ := fun y => betaMeasure (α + successes y) (β + ((n - successes y : ℕ) : ℝ)))
    (c := fun y => ENNReal.ofReal
      (beta (α + successes y) (β + ((n - successes y : ℕ) : ℝ)) / beta α β))
    (measurable_uncurry_prod_likelihood measurable_uncurry_bernoulliDensity)
    (fun θ => iidKernel_withDensity measurable_uncurry_bernoulliDensity hbern n θ)
    (fun y => isProbabilityMeasureBeta (add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg _))
      (add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg _))) ?_
  intro y
  have hg : Measurable (fun θ => ∏ i, bernoulliDensity θ (y i)) :=
    (measurable_uncurry_prod_likelihood measurable_uncurry_bernoulliDensity).comp
      (measurable_id.prodMk measurable_const)
  have hck : ENNReal.ofReal
      (beta (α + successes y) (β + ((n - successes y : ℕ) : ℝ)) / beta α β) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hdens : betaPDF α β * (fun θ => ∏ i, bernoulliDensity θ (y i))
      = (ENNReal.ofReal
          (beta (α + successes y) (β + ((n - successes y : ℕ) : ℝ)) / beta α β))
        • betaPDF (α + successes y) (β + ((n - successes y : ℕ) : ℝ)) := by
    funext θ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [prod_bernoulliDensity θ y,
      betaPDF_mul_clampPow hα hβ (successes y) (n - successes y) θ]
  simp only [betaMeasure]
  rw [← withDensity_mul _ hbeta hg, hdens, withDensity_smul' _ _ hck]

/-- **Laplace's rule of succession** (Gelman §2.4): the posterior predictive
probability of one more success after `n` tosses with `s` successes is `(α + s)/(α + β + n)`,
predictive-a.e. -/
theorem beta_bernoulli_posteriorPredictive_true_ae {α β : ℝ}
    -- USER-INPUT: positive Beta parameters; Gelman §2.4
    (hα : 0 < α) (hβ : 0 < β)
    -- LEAN-ONLY: instance plumbing, derivable from hα/hβ via `isProbabilityMeasureBeta`
    [IsFiniteMeasure (betaMeasure α β)] (n : ℕ) :
    ∀ᵐ y ∂(iidKernel bernoulliKernel n ∘ₘ betaMeasure α β),
      posteriorPredictive (iidKernel bernoulliKernel n) bernoulliKernel (betaMeasure α β) y {true}
        = ENNReal.ofReal ((α + successes y) / (α + β + n)) := by
  have hbk : ∀ θ, bernoulliKernel θ {true} = ENNReal.ofReal (unitClamp θ) := by
    intro θ
    rw [bernoulliKernel, Kernel.withDensity_apply _ measurable_uncurry_bernoulliDensity,
      Kernel.const_apply, withDensity_apply _ (measurableSet_singleton true),
      ← lintegral_indicator (measurableSet_singleton true), lintegral_count, tsum_fintype,
      Fintype.sum_bool]
    simp [bernoulliDensity, Set.indicator]
  filter_upwards [beta_bernoulli_posterior_ae hα hβ n] with y hy
  have hle : successes y ≤ n := by
    rw [successes]
    calc ∑ i, (y i).toNat ≤ ∑ _i : Fin n, 1 :=
          Finset.sum_le_sum (fun i _ => by cases y i <;> simp)
      _ = n := by simp
  rw [posteriorPredictive_apply, hy,
    Measure.bind_apply (measurableSet_singleton true) bernoulliKernel.measurable.aemeasurable,
    lintegral_congr hbk,
    lintegral_unitClamp_betaMeasure (add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg _))
      (add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg _))]
  congr 1
  rw [Nat.cast_sub hle]
  ring

end StatLean.Bayesian
