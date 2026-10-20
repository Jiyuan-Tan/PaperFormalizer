module
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.MeasureTheory.Measure.Count

@[expose] public section

/-!
# Conjugacy — core data model (likelihood kernels and the exponential-family conjugate prior)

Data model for the conjugate-prior theorems:

* **clamped likelihood families** making textbook models total kernels over `Θ = ℝ`:
  `unitClamp` (success probabilities), Bernoulli/Binomial densities and kernels over counting
  measure, the Poisson kernel (rate clamped by `Real.toNNReal`), and the Gaussian
  known-variance kernel over Lebesgue measure;
* sample statistics `successes` (Bernoulli) and the Normal-Normal posterior parameters
  `postVar`/`postMean`;
* the **natural exponential family** `expFamilyDensity η T A h` with statistic `T`, natural
  parameter `η(θ)`, log-partition `A`, and base factor `h`; its **Diaconis–Ylvisaker conjugate
  prior** `conjExpPrior` with hyperparameters `(χ, ν₀)` and abstract normalization `conjExpZ`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §3.3.3, Definition 3.3.2/eq. (3.3.1) (exponential families) and
Proposition 3.3.13/eqs. (3.3.4)–(3.3.5) (the natural conjugate family), pp. 115–120; Table 3.3.1,
p. 121; Appendix A.2/A.3/A.10/A.12 (Gamma, Beta, Binomial, Poisson densities), pp. 519–521.

**Proof formalization notes.** Laptop-only data model — definitions only. Clamping makes every
kernel total and (except the Gaussian at `v = 0`) Markov for *all* real parameters, while the
conjugate identities hold pointwise because the Beta/Gamma prior densities vanish off the
parameter's support. Discrete kernels are `Kernel.withDensity` of `Kernel.const _ Measure.count`
(σ-finite on countable types with measurable singletons). The Gaussian kernel is `withDensity` of
Lebesgue with `gaussianPDF θ v ·`; at `v = 0` it degenerates to the zero kernel (junk, documented),
and the Markov instance carries `v ≠ 0` (`Conjugacy.NormalNormal`). The conjugate-prior
normalization `conjExpZ` is kept **abstract**: the update and marginal theorems only ever need
`0 < Z < ∞`, which is Robert's propriety condition (3.3.5) — a genuine user input, not a derivable
fact.

**Bibliographic comments.** Conjugate priors originate with H. Raiffa and R. Schlaifer, *Applied
Statistical Decision Theory* (Harvard, 1961); the exponential-family theory
of conjugacy — including the linearity of posterior expectations characterizing these priors — is
P. Diaconis and D. Ylvisaker, "Conjugate priors for exponential families," *Ann. Statist.* 7
(1979), 269–281. The general theory of exponential families is L. D. Brown, *Fundamentals of
Statistical Exponential Families* (IMS Lecture Notes 9, 1986).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-! ### Clamps and sample statistics -/

/-- Clamp a real parameter into `[0, 1]` (success probabilities). Off `[0, 1]` the clamped
likelihoods below are still probability vectors, and priors supported on `[0, 1]` never see the
difference. -/
noncomputable def unitClamp (θ : ℝ) : ℝ := max 0 (min 1 θ)

/-- Number of successes in a Bernoulli sample. -/
def successes {n : ℕ} (y : Fin n → Bool) : ℕ := ∑ i, (y i).toNat

/-! ### Bernoulli and Binomial kernels (Robert Appendix A.10) -/

/-- Bernoulli density (pmf against counting measure on `Bool`) with clamped success
probability. -/
noncomputable def bernoulliDensity : ℝ → Bool → ℝ≥0∞ :=
  fun θ b => ENNReal.ofReal (if b then unitClamp θ else 1 - unitClamp θ)

/-- The Bernoulli kernel over `Θ = ℝ` (clamped success probability). -/
noncomputable def bernoulliKernel : Kernel ℝ Bool :=
  Kernel.withDensity (Kernel.const ℝ Measure.count) bernoulliDensity

/-- Binomial density (pmf against counting measure on `Fin (n+1)`) with clamped success
probability: `C(n,k) θ^k (1−θ)^(n−k)` (Robert Appendix A.10). -/
noncomputable def binomialDensity (n : ℕ) : ℝ → Fin (n + 1) → ℝ≥0∞ :=
  fun θ k =>
    ENNReal.ofReal ((n.choose k : ℝ) * unitClamp θ ^ (k : ℕ) * (1 - unitClamp θ) ^ (n - (k : ℕ)))

/-- The Binomial kernel `θ ↦ ℬ(n, θ)` over `Θ = ℝ` (clamped success probability). -/
noncomputable def binomialKernel (n : ℕ) : Kernel ℝ (Fin (n + 1)) :=
  Kernel.withDensity (Kernel.const ℝ Measure.count) (binomialDensity n)

/-! ### Poisson kernel (Robert Appendix A.12) -/

/-- Poisson density (pmf against counting measure on `ℕ`) with the rate clamped by
`Real.toNNReal`; reuses the pinned `poissonPMFReal`. -/
noncomputable def poissonDensity : ℝ → ℕ → ℝ≥0∞ :=
  fun θ k => ENNReal.ofReal (poissonPMFReal θ.toNNReal k)

/-- The Poisson kernel `θ ↦ 𝒫(θ⁺)` over `Θ = ℝ` (rate clamped at `0`; the rate-`0` Poisson is the
Dirac mass at `0`, still a probability). -/
noncomputable def poissonKernel : Kernel ℝ ℕ :=
  Kernel.withDensity (Kernel.const ℝ Measure.count) poissonDensity

/-! ### Gaussian known-variance kernel -/

/-- The Gaussian kernel `θ ↦ 𝒩(θ, v)` over `Θ = ℝ`, as a Lebesgue density kernel. Junk: the zero
kernel at `v = 0` (the pdf vanishes); the Markov instance carries `v ≠ 0`. -/
noncomputable def gaussKernel (v : ℝ≥0) : Kernel ℝ ℝ :=
  Kernel.withDensity (Kernel.const ℝ volume) fun θ x => gaussianPDF θ v x

/-- Posterior variance of the Normal-Normal model with prior variance `t₀`, noise variance `v`,
and `n` observations: `(t₀⁻¹ + n·v⁻¹)⁻¹` (Robert Table 3.3.1 / §4.4.1). -/
noncomputable def postVar (t₀ v : ℝ≥0) (n : ℕ) : ℝ≥0 := (t₀⁻¹ + n * v⁻¹)⁻¹

/-- Posterior mean of the Normal-Normal model: precision-weighted combination of the prior mean
and the sample sum (Robert Table 3.3.1 / Table 4.2.1). -/
noncomputable def postMean (m₀ : ℝ) (t₀ v : ℝ≥0) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (postVar t₀ v n : ℝ) * (m₀ / (t₀ : ℝ) + (∑ i, x i) / (v : ℝ))

/-! ### Natural exponential families and their conjugate priors (Robert §3.3.3) -/

variable {d : ℕ}

/-- **Natural exponential family density** with natural parameter `η(θ) ∈ ℝ^d`, sufficient
statistic `T(x) ∈ ℝ^d`, log-partition `A(θ)`, and base factor `h(x)`:
`p(θ, x) = h(x) · exp(⟨η θ, T x⟩ − A θ)` (Robert Definition 3.3.2 / eq. (3.3.3)). -/
noncomputable def expFamilyDensity (η : Θ → Fin d → ℝ) (T : 𝓧 → Fin d → ℝ)
    (A : Θ → ℝ) (h : 𝓧 → ℝ≥0∞) : Θ → 𝓧 → ℝ≥0∞ :=
  fun θ x => h x * ENNReal.ofReal (Real.exp (∑ i, η θ i * T x i - A θ))

/-- **Conjugate-prior weight** with hyperparameters `(χ, ν₀)`:
`exp(⟨χ, η θ⟩ − ν₀ · A θ)` (Robert eq. (3.3.4)). -/
noncomputable def conjExpWeight (η : Θ → Fin d → ℝ) (A : Θ → ℝ)
    (χ : Fin d → ℝ) (ν₀ : ℝ) : Θ → ℝ≥0∞ :=
  fun θ => ENNReal.ofReal (Real.exp (∑ i, χ i * η θ i - ν₀ * A θ))

/-- **Conjugate-prior normalization** `Z(χ, ν₀) = ∫ exp(⟨χ, η θ⟩ − ν₀ A θ) μ₀(dθ)` against the
base measure `μ₀`. Kept abstract: propriety `0 < Z < ∞` is Robert's condition (3.3.5), a genuine
input. -/
noncomputable def conjExpZ (μ₀ : Measure Θ) (η : Θ → Fin d → ℝ) (A : Θ → ℝ)
    (χ : Fin d → ℝ) (ν₀ : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, conjExpWeight η A χ ν₀ θ ∂μ₀

/-- **The Diaconis–Ylvisaker conjugate prior** `π(θ | χ, ν₀) ∝ exp(⟨χ, η θ⟩ − ν₀ A θ)` against
`μ₀` (Robert Proposition 3.3.13, eq. (3.3.4)). Junk: the zero measure when `Z ∈ {0, ∞}`. -/
noncomputable def conjExpPrior (μ₀ : Measure Θ) (η : Θ → Fin d → ℝ) (A : Θ → ℝ)
    (χ : Fin d → ℝ) (ν₀ : ℝ) : Measure Θ :=
  (conjExpZ μ₀ η A χ ν₀)⁻¹ • μ₀.withDensity (conjExpWeight η A χ ν₀)

end StatLean.Bayesian
