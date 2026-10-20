module
public import StatLean.Bayesian.EmpiricalBayes.Defs
public import StatLean.Bayesian.Conjugacy.Defs

@[expose] public section

/-!
# Robbins's nonparametric empirical Bayes rule (Poisson)

Robbins's celebrated formula: for a Poisson likelihood with any mixing distribution `G` on the
rate, the posterior mean of the rate given a count `y` is
$$\mathbb E[\theta \mid Y = y] = (y+1)\,\frac{f_G(y+1)}{f_G(y)},$$
expressed entirely through the marginal pmf `f_G`, which empirical Bayes estimates from data — no
knowledge of `G` is needed. The plug-in estimator using the empirical pmf is consistent.

**Reference.** Not in Robert (Robert §10.4.1 discusses nonparametric EB but not this identity).
H. Robbins, "An empirical Bayes approach to statistics," *Proc. Third Berkeley Symp. Math. Statist.
Probab.* 1 (1956), 157–163, eq. (5); see also B. Efron, *Large-Scale Inference*, Cambridge
University Press, 2010, §6.1.

**Proof formalization notes.** The identity rests on the Poisson pmf recursion
`(y+1)·p_{y+1}(θ) = θ·p_y(θ)` (`poissonDensity_succ_mul`, pure `Nat`/`Real` algebra on
`e^{-θ}θ^y/y!`); integrating against `G` and pulling the constant `(y+1)` out of `∫⁻` gives the
numerator of the posterior mean as `(y+1)·f_G(y+1)`. Consistency is the continuous-mapping /
quotient limit of the plug-in empirical pmf (`strong_law` for the counts).

**Bibliographic comments.** Robbins's empirical Bayes (1951, 1956) is the origin of the whole
subject; the Poisson formula is its signature example (Efron 2010, §6). Its modern nonparametric
form and the g-modeling alternative are due to B. Efron ("Empirical Bayes deconvolution estimates,"
*Biometrika* 103 (2016), 1–20) and W. Jiang and C.-H. Zhang ("General maximum likelihood empirical
Bayes estimation of normal means," *Ann. Statist.* 37 (2009), 1647–1684).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace StatLean.Bayesian

/-- **Robbins's Poisson empirical Bayes estimator** `(y+1)·f_G(y+1)/f_G(y)` (Robbins 1956). -/
noncomputable def robbinsPoissonEstimator (G : Measure ℝ) (y : ℕ) : ℝ≥0∞ :=
  ((y : ℝ≥0∞) + 1) * mixtureDensity poissonDensity G (y + 1) / mixtureDensity poissonDensity G y

/-- **Poisson pmf recursion**: `(y+1)·p_{y+1}(θ) = θ·p_y(θ)` (the algebra behind Robbins's rule). -/
theorem poissonDensity_succ_mul (θ : ℝ)
    -- USER-INPUT: nonnegative Poisson rate; Robbins 1956
    (hθ : 0 ≤ θ) (y : ℕ) :
    ((y : ℝ≥0∞) + 1) * poissonDensity θ (y + 1) = ENNReal.ofReal θ * poissonDensity θ y := by
  unfold poissonDensity
  have hy : ((y : ℝ≥0∞) + 1) = ENNReal.ofReal ((y : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [hy, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hθ]
  congr 1
  simp only [poissonPMFReal, Real.coe_toNNReal θ hθ]
  have h1 : (y.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero y)
  have h2 : ((y : ℝ) + 1) ≠ 0 := by positivity
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- **Robbins's identity** (3F.4): the numerator of the Poisson posterior mean equals
`(y+1)·f_G(y+1)` (Robbins 1956). -/
theorem robbins_poisson_posteriorMean (G : Measure ℝ) [IsProbabilityMeasure G]
    -- USER-INPUT: the mixing measure charges only nonnegative rates; Robbins 1956
    (hG : ∀ᵐ θ ∂G, 0 ≤ θ) (y : ℕ) :
    ∫⁻ θ, ENNReal.ofReal θ * poissonDensity θ y ∂G
      = ((y : ℝ≥0∞) + 1) * mixtureDensity poissonDensity G (y + 1) := by
  unfold mixtureDensity predictiveDensity
  rw [← lintegral_const_mul' ((y : ℝ≥0∞) + 1) _ (by simp)]
  refine lintegral_congr_ae ?_
  filter_upwards [hG] with θ hθ
  exact (poissonDensity_succ_mul θ hθ y).symm

/-- **Consistency of the plug-in Robbins estimator** (3F.5): if the empirical marginal pmf converges
to the true marginal pmf, the plug-in Robbins estimator converges to the oracle (Robbins 1956). -/
theorem robbinsEstimator_tendsto_oracle (G : Measure ℝ) [IsProbabilityMeasure G] (y : ℕ)
    (fhat : ℕ → ℕ → ℝ≥0∞)
    -- USER-INPUT: the empirical pmf is consistent for the marginal pmf; Robbins 1956 / SLLN
    (hf : ∀ k, Tendsto (fun n => fhat n k) atTop (𝓝 (mixtureDensity poissonDensity G k)))
    -- USER-INPUT: the marginal pmf is nondegenerate at `y`
    (hpos : mixtureDensity poissonDensity G y ≠ 0) (htop : mixtureDensity poissonDensity G y ≠ ∞) :
    Tendsto (fun n => ((y : ℝ≥0∞) + 1) * fhat n (y + 1) / fhat n y) atTop
      (𝓝 (robbinsPoissonEstimator G y)) := by
  unfold robbinsPoissonEstimator
  exact ENNReal.Tendsto.div
    (ENNReal.Tendsto.const_mul (hf (y + 1)) (Or.inr (by simp)))
    (Or.inr hpos) (hf y) (Or.inl htop)

end StatLean.Bayesian
