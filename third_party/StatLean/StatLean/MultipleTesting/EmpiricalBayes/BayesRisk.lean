module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# Bayes risk of the Gaussian shrinkage (empirical-Bayes) estimator

Consider the Gaussian sequence model with a Gaussian prior: the coordinates of the unknown mean
are drawn from a prior $\theta_i \sim N(0, \tau^2)$, the data are observed with independent
Gaussian noise $\varepsilon_i \sim N(0, \sigma^2)$ (with $\theta_i \perp \varepsilon_i$), and we
see $X_i = \theta_i + \varepsilon_i$. The Bayes estimator — the posterior mean — shrinks the data
toward zero by the factor $s = \tau^2/(\sigma^2 + \tau^2)$:
$$\hat\mu_{B,i} = s\, X_i = \frac{\tau^2}{\sigma^2 + \tau^2}\,(\theta_i + \varepsilon_i).$$

The result formalized here is that the resulting Bayes risk equals the maximum-likelihood
(no-shrinkage) risk multiplied by the same shrinkage factor:
$$\mathbb{E}\,\lVert \hat\mu_B - \theta \rVert^2
   = p\,\frac{\sigma^2\tau^2}{\sigma^2 + \tau^2}
   = R_{\mathrm{MLE}} \cdot \frac{\tau^2}{\sigma^2 + \tau^2},
   \qquad R_{\mathrm{MLE}} = \mathbb{E}\,\lVert X - \theta \rVert^2 = p\,\sigma^2.$$
Since $\tau^2/(\sigma^2+\tau^2) < 1$, shrinkage strictly reduces the risk, and the reduction is
largest when the signal-to-noise ratio $\tau^2/\sigma^2$ is small.

The Lean statement requires $\sigma^2 > 0$ and $\tau^2 > 0$ and takes each coordinate's law and the
within-coordinate independence $\theta_i \perp \varepsilon_i$ as explicit hypotheses; it states the
risk of the fixed estimator above and does not separately introduce the symbol $R_{\mathrm{MLE}}$
(the identity $R_{\mathrm{MLE}} = p\sigma^2$ is recorded only in this prose).

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University,
2023, Lecture 15 (An Empirical Bayes Interpretation of the James–Stein Estimator), §15.3.3 (Bayes
Risk), Proposition 1. The shrinkage estimator is Eq (15.3); the prior/noise setup is Eqs
(15.1)–(15.2).

**Proof formalization notes.** Per coordinate, the residual is
$\hat\mu_{B,i} - \theta_i = (s-1)\theta_i + s\,\varepsilon_i = -\rho\,\theta_i + s\,\varepsilon_i$,
where $\rho = 1 - s = \sigma^2/(\sigma^2+\tau^2)$. By independence and
$\mathbb{E}[\theta_i] = \mathbb{E}[\varepsilon_i] = 0$, the cross term vanishes, so
$$\mathbb{E}[(\hat\mu_{B,i} - \theta_i)^2]
   = \rho^2\,\mathbb{E}[\theta_i^2] + s^2\,\mathbb{E}[\varepsilon_i^2]
   = \rho^2\tau^2 + s^2\sigma^2 = \frac{\sigma^2\tau^2}{\sigma^2+\tau^2};$$
summing over the $p$ coordinates gives the claim. The second moments
$\mathbb{E}[\theta_i^2] = \tau^2$ and $\mathbb{E}[\varepsilon_i^2] = \sigma^2$ are the Gaussian
second moments (variance $+$ mean$^2$). The book conditions on $\mu$ and then takes an outer
expectation; the formalization works directly with the unconditional second moments, which is
equivalent and avoids the conditional-expectation machinery.

**Bibliographic comments.** The normal–normal conjugate computation of this Bayes risk is
classical/folklore: it is the standard consequence of the posterior $\mu \mid X$ being Gaussian
with the reduced variance $\nu = \tau^2\sigma^2/(\tau^2+\sigma^2)$, and as such has no single
seminal origin. Its use as the *empirical-Bayes* interpretation of the James–Stein estimator — the
role it plays in Candès Lecture 15 — originates with B. Efron and C. Morris, "Stein's Estimation
Rule and Its Competitors—An Empirical Bayes Approach", *Journal of the American Statistical
Association* 68(341) (1973), 117–130, who recover the James–Stein rule by plugging an unbiased
estimate $(p-2)\sigma^2/\lVert X\rVert^2$ of the shrinkage factor into this Bayes estimator.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `E[Z²] = v` for `Z ∼ N(0,v)` (second moment = variance, mean `0`); the `v = 1` case is the
merged `ForMathlib/GaussianMoments.lean` `integral_sq_stdGaussian`, here for arbitrary variance. -/
private lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral (by fun_prop)] at hv
  simpa using hv

/-- Integrability of `x ↦ x²` against `N(0,v)`, read off from `id ∈ L²` (`memLp_id_gaussianReal'`),
mirroring `GaussianMoments.lean`'s `integrable_pow_stdGaussian`. -/
private lemma integrable_sq_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  have h : Integrable (fun x : ℝ => ‖id x‖ ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' (μ := 0) (v := v) ((2 : ℕ) : ℝ≥0∞)
      (by simp)).integrable_norm_pow (p := 2) (by norm_num)
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [id, Real.norm_eq_abs]

/-- The per-coordinate facts pushed through the Gaussian law: a measurable `X` with
`Measure.map X μ = N(0,v)` is integrable, its square is integrable, its mean is `0`, and its second
moment is `v`. Used for both the prior coordinate `θᵢ` (`v = τ²`) and noise `εᵢ` (`v = σ²`). -/
private lemma coord_facts (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {v : ℝ} (hv : 0 < v)
    (hlaw : Measure.map X μ = gaussianReal 0 ⟨v, hv.le⟩) :
    Integrable X μ ∧ Integrable (fun ω => (X ω) ^ 2) μ ∧
      (∫ ω, X ω ∂μ = 0) ∧ (∫ ω, (X ω) ^ 2 ∂μ = v) := by
  set w : ℝ≥0 := ⟨v, hv.le⟩ with hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `Integrable X μ`: `id ∈ L¹(N(0,v))`, transported through `Measure.map X μ`.
    have hL1 : Integrable (fun y : ℝ => y) (gaussianReal 0 w) :=
      (memLp_id_gaussianReal' (μ := 0) (v := w) 1 (by simp)).integrable le_rfl
    rw [← hlaw] at hL1
    have := (integrable_map_measure hL1.aestronglyMeasurable hX.aemeasurable).mp hL1
    simpa [Function.comp] using! this
  · -- `Integrable X² μ`: same transport for `x ↦ x²`.
    have hL2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 w) :=
      integrable_sq_gaussianReal _
    rw [← hlaw] at hL2
    have := (integrable_map_measure hL2.aestronglyMeasurable hX.aemeasurable).mp hL2
    simpa [Function.comp] using! this
  · -- `E[X] = 0` via `integral_map` and `integral_id_gaussianReal`.
    have h : ∫ y, y ∂(Measure.map X μ) = ∫ ω, X ω ∂μ :=
      integral_map hX.aemeasurable (f := fun y => y) (by fun_prop)
    rw [← h, hlaw, integral_id_gaussianReal]
  · -- `E[X²] = v` via `integral_map` and `integral_sq_gaussianReal`.
    have h : ∫ y, y ^ 2 ∂(Measure.map X μ) = ∫ ω, (X ω) ^ 2 ∂μ :=
      integral_map hX.aemeasurable (f := fun y => y ^ 2) (by fun_prop)
    rw [← h, hlaw]
    simp [integral_sq_gaussianReal]
    rfl

/-- **Empirical-Bayes / Bayes risk of the Gaussian shrinkage estimator** (Candès, Lecture 15,
§15.3.3, Proposition 1, STAT 300C). For a Gaussian prior `θᵢ ∼ N(0,τ²)` and independent noise
`εᵢ ∼ N(0,σ²)`, the shrinkage estimator `μ̂_B,ᵢ = (τ²/(σ²+τ²))·(θᵢ+εᵢ)` has Bayes risk
`E‖μ̂_B − θ‖² = p·σ²τ²/(σ²+τ²)` ( `= R_MLE · τ²/(σ²+τ²)`, `R_MLE = pσ²`). -/
theorem empiricalBayes_risk {p : ℕ} {σ2 τ2 : ℝ} (hσ : 0 < σ2) (hτ : 0 < τ2)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (θ ε : Fin p → Ω → ℝ)
    -- USER-INPUT: each prior coordinate is measurable; Candès L15 §15.3.3
    (hθmeas : ∀ i, Measurable (θ i))
    -- USER-INPUT: each noise coordinate is measurable; Candès L15 §15.3.3
    (hεmeas : ∀ i, Measurable (ε i))
    -- USER-INPUT: prior θᵢ ∼ N(0, τ²); Candès L15 §15.3.3
    (hθlaw : ∀ i, Measure.map (θ i) μ = gaussianReal 0 ⟨τ2, hτ.le⟩)
    -- USER-INPUT: noise εᵢ ∼ N(0, σ²); Candès L15 §15.3.3
    (hεlaw : ∀ i, Measure.map (ε i) μ = gaussianReal 0 ⟨σ2, hσ.le⟩)
    -- USER-INPUT: prior and noise are independent within each coordinate; Candès L15 §15.3.3
    (hindep : ∀ i, IndepFun (θ i) (ε i) μ) :
    (∫ ω, ∑ i, ((τ2 / (σ2 + τ2)) * (θ i ω + ε i ω) - θ i ω) ^ 2 ∂μ)
      = (p : ℝ) * (σ2 * τ2 / (σ2 + τ2)) := by
  have hden : 0 < σ2 + τ2 := by positivity
  have hd : σ2 + τ2 ≠ 0 := ne_of_gt hden
  -- Per coordinate: integrability of the squared residual, and its integral.
  have key : ∀ i, Integrable (fun ω => ((τ2 / (σ2 + τ2)) * (θ i ω + ε i ω) - θ i ω) ^ 2) μ
      ∧ ∫ ω, ((τ2 / (σ2 + τ2)) * (θ i ω + ε i ω) - θ i ω) ^ 2 ∂μ = σ2 * τ2 / (σ2 + τ2) := by
    intro i
    obtain ⟨hθint, hθsqint, hθ0, hθsq⟩ := coord_facts μ (hθmeas i) hτ (hθlaw i)
    obtain ⟨hεint, hεsqint, hε0, hεsq⟩ := coord_facts μ (hεmeas i) hσ (hεlaw i)
    set s := τ2 / (σ2 + τ2) with hsdef
    -- cross term: `θᵢ·εᵢ` integrable and `E[θᵢ·εᵢ] = E[θᵢ]·E[εᵢ] = 0`.
    have hcrossint : Integrable (fun ω => θ i ω * ε i ω) μ := (hindep i).integrable_mul hθint hεint
    have hcross0 : ∫ ω, θ i ω * ε i ω ∂μ = 0 := by
      have hmul := (hindep i).integral_fun_mul_eq_mul_integral
        (hθmeas i).aestronglyMeasurable (hεmeas i).aestronglyMeasurable
      have e1 : μ[θ i] = 0 := hθ0
      have e2 : μ[ε i] = 0 := hε0
      rw [hmul, e1, e2, mul_zero]
    -- pointwise expansion of the squared residual `((s-1)θ + sε)²`.
    have hexp : ∀ ω, (s * (θ i ω + ε i ω) - θ i ω) ^ 2
        = (s - 1) ^ 2 * (θ i ω) ^ 2 + s ^ 2 * (ε i ω) ^ 2
          + (2 * s * (s - 1)) * (θ i ω * ε i ω) := fun ω => by ring
    have h1 : Integrable (fun ω => (s - 1) ^ 2 * (θ i ω) ^ 2) μ := hθsqint.const_mul _
    have h2 : Integrable (fun ω => s ^ 2 * (ε i ω) ^ 2) μ := hεsqint.const_mul _
    have h3 : Integrable (fun ω => (2 * s * (s - 1)) * (θ i ω * ε i ω)) μ := hcrossint.const_mul _
    have h12 : Integrable (fun ω => (s - 1) ^ 2 * (θ i ω) ^ 2 + s ^ 2 * (ε i ω) ^ 2) μ := h1.add h2
    have hresint : Integrable (fun ω => (s * (θ i ω + ε i ω) - θ i ω) ^ 2) μ :=
      (h12.add h3).congr (Filter.Eventually.of_forall (fun ω => (hexp ω).symm))
    refine ⟨hresint, ?_⟩
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
        integral_add h12 h3, integral_add h1 h2,
        integral_const_mul, integral_const_mul, integral_const_mul, hθsq, hεsq, hcross0, hsdef]
    field_simp
    ring
  -- Sum out: `∫ ∑ = ∑ ∫ = ∑ σ²τ²/(σ²+τ²) = p · σ²τ²/(σ²+τ²)`.
  have hval : ∀ i, ∫ ω, ((τ2 / (σ2 + τ2)) * (θ i ω + ε i ω) - θ i ω) ^ 2 ∂μ
      = σ2 * τ2 / (σ2 + τ2) := fun i => (key i).2
  rw [integral_finset_sum Finset.univ (fun i _ => (key i).1)]
  simp_rw [hval]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end StatLean.MultipleTesting
