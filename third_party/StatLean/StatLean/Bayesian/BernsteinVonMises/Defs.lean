module
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
public import StatLean.Bayesian.ForMathlib.IIDKernel
public import StatLean.Bayesian.ForMathlib.TVDist
public import Mathlib.Probability.Kernel.Posterior

@[expose] public section

/-!
# Bernstein–von Mises: local model, tests, and prior conditions (data model)

Data model for vdV Chapter 10. The observations are an iid sample from a dominated parametric
family `M : ParametricFamily 𝓧 (ℝ^k)` with dominating measure `μ`; the prior is a probability
measure `π` on the parameter space. Objects:

* `bvmLocalScale θ₀ n` — the local rescaling `θ ↦ √n (θ − θ₀)` (junk at `n = 0`: constant `0`);
* `bvmLocalPosterior κ π θ₀ n` — the posterior of the **local parameter** `h = √n(θ − θ₀)`
  given an `n`-sample: the pushforward of the posterior kernel `(iidKernel κ n)†π` under
  `bvmLocalScale θ₀ n`;
* `bvmEffScore J sc n` — vdV's centering sequence `Δ_{n,θ₀} = J⁻¹ · (n^{-1/2} ∑ᵢ sc(Xᵢ))`
  (Chapter-10 convention: the *efficient* normalized score, carrying `J⁻¹ = I_{θ₀}⁻¹`;
  Chapters 7–8 use the un-multiplied score sum);
* `bvmGaussian J sc n ω` — the random Gaussian approximation `N(Δ_{n,θ₀}, J⁻¹)`;
* `bvmTV` — the (sup-form) total-variation distance between the two, the quantity that the
  Bernstein–von Mises theorem sends to `0` in probability;
* `UniformlyConsistentTests` — the uniform-tests condition;
* `IsExpConsistentTestSeq` — the conclusion shape of the exponential-tests lemma (exponentially
powerful
  tests);
* `HasLocalDensity` — the prior condition of the Bernstein–von Mises theorem: absolute continuity in
a
  neighborhood of `θ₀` with a Lebesgue density continuous and positive at `θ₀` (the prior is
  arbitrary outside the neighborhood).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.2, pp. 139–141: the local reparametrization `h = √n(θ − θ₀)` (p. 139), the
centering `Δ_{n,θ₀} = n^{-1/2} ∑ I_{θ₀}^{-1} ℓ̇_{θ₀}(Xᵢ)` (p. 140), the tests condition
(10.2) and the prior condition (Theorem 10.1, p. 141).

**Proof formalization notes.** Laptop-only data model — definitions and trivial wiring only.
The posterior object is Mathlib's canonical `ProbabilityTheory.posterior` (`κ†π`); vdV's
total-variation norm `‖·‖` is `2 · tvDist` (sup-form vs `L¹`-form) — immaterial for the
convergence-to-zero statements, recorded here once. The tests conditions avoid `iSup` over
uncountable parameter sets by unrolling suprema into eventually-uniform bounds.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum)
open StatLean.Minimaxity (tvDist)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- The local rescaling `θ ↦ √n (θ − θ₀)` of vdV p. 139. Junk behavior: at `n = 0` the map is
constant `0` (`√0 = 0`); all asymptotic statements below are eventual in `n`. -/
noncomputable def bvmLocalScale (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
  fun θ => (Real.sqrt n) • (θ - θ₀)

lemma measurable_bvmLocalScale (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    Measurable (bvmLocalScale θ₀ n) := by
  unfold bvmLocalScale; fun_prop

/-- The inverse local map `h ↦ θ₀ + h/√n` (a genuine two-sided inverse of
`bvmLocalScale θ₀ n` for `n ≥ 1`). -/
noncomputable def bvmLocalUnscale (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
  fun h => θ₀ + (Real.sqrt n)⁻¹ • h

lemma measurable_bvmLocalUnscale (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    Measurable (bvmLocalUnscale θ₀ n) := by
  unfold bvmLocalUnscale; fun_prop



/-- **Local-parameter posterior**: the posterior law of `h = √n(θ − θ₀)` given the `n`-sample,
as a kernel `(Fin n → 𝓧) ⤳ ℝ^k`: the pushforward of the canonical posterior
`(iidKernel κ n)†π` under `bvmLocalScale θ₀ n` (vdV p. 139, second display). -/
noncomputable def bvmLocalPosterior (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧)
    [IsMarkovKernel κ] (π : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure π]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    Kernel (Fin n → 𝓧) (EuclideanSpace ℝ (Fin k)) :=
  Kernel.map ((iidKernel κ n)†π) (bvmLocalScale θ₀ n)

instance (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧) [IsMarkovKernel κ]
    (π : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure π]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    IsMarkovKernel (bvmLocalPosterior κ π θ₀ n) :=
  Kernel.IsMarkovKernel.map _ (measurable_bvmLocalScale θ₀ n)

/-- **vdV's Chapter-10 centering sequence** `Δ_{n,θ₀} = J⁻¹ ((1/√n) ∑ᵢ sc(ωᵢ))` — the
normalized score sum pre-multiplied by the inverse Fisher information (p. 140). Note the
`J⁻¹`: Chapters 7–8 use the plain `scoreSum`. -/
noncomputable def bvmEffScore (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    EuclideanSpace ℝ (Fin k) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ (scoreSum sc n ω)


/-- The **random Gaussian approximation** `N(Δ_{n,θ₀}, J⁻¹)` of the Bernstein–von Mises theorem. -/
noncomputable def bvmGaussian (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  multivariateGaussian (bvmEffScore J sc n ω) J⁻¹

/-- The **Bernstein–von Mises deviation**: the (sup-form) total-variation distance between the
local posterior and its Gaussian approximation, as a function of the sample. vdV's `‖·‖` is
twice this quantity. -/
noncomputable def bvmTV (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧) [IsMarkovKernel κ]
    (π : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure π]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  tvDist (bvmLocalPosterior κ π θ₀ n ω) (bvmGaussian J sc n ω)

/-- **The the uniform-tests condition**: for every `ε > 0` there are tests `φₙ : 𝓧ⁿ → [0,1]` with
`P^n_{θ₀} φₙ → 0` and `sup_{‖θ−θ₀‖ ≥ ε} P^n_θ (1 − φₙ) → 0`. The supremum over the
(uncountable) alternative is unrolled into an eventually-uniform bound. -/
def UniformlyConsistentTests (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧) (θ₀ : EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ,
      (∀ n, Measurable (φ n)) ∧ (∀ n ω, φ n ω ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun n => ∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ θ, ε ≤ ‖θ - θ₀‖ →
        ∫ ω, (1 - φ n ω) ∂(productMeasure M μ θ n) ≤ δ

/-- **Exponentially powerful test sequence** — the conclusion shape of vdV §10.2: tests
with vanishing size at `θ₀` and type-II error `≤ exp(−c n (‖θ−θ₀‖² ∧ 1))` uniformly over
`‖θ − θ₀‖ ≥ Mₙ/√n`, for `n` large. -/
structure IsExpConsistentTestSeq (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧) (θ₀ : EuclideanSpace ℝ (Fin k)) (Mseq : ℕ → ℝ) (c : ℝ)
    (φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ) : Prop where
  /-- Constitutive (vdV p. 141 footnote): a test is a measurable `[0,1]`-valued statistic. -/
  measurable : ∀ n, Measurable (φ n)
  /-- Constitutive (vdV p. 141 footnote): tests take values in `[0,1]`. -/
  mem_Icc : ∀ n ω, φ n ω ∈ Set.Icc (0 : ℝ) 1
  /-- Constitutive (vdV §10.2): the size at the true parameter vanishes,
  `P^n_{θ₀} φₙ → 0`. -/
  typeI : Tendsto (fun n => ∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) atTop (𝓝 0)
  /-- Constitutive (vdV §10.2): the exponential type-II bound
  `P^n_θ(1 − φₙ) ≤ exp(−c n (‖θ−θ₀‖² ∧ 1))` for all `‖θ − θ₀‖ ≥ Mₙ/√n` and `n` large. -/
  typeII : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ θ, Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖ →
    ∫ ω, (1 - φ n ω) ∂(productMeasure M μ θ n)
      ≤ Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)

/-- **The prior condition of the Bernstein–von Mises theorem**: `π` is absolutely continuous on the
ball
`B(θ₀, r₀)` with a Lebesgue density `f` continuous and positive at `θ₀`; outside the ball
`π` is arbitrary. -/
structure HasLocalDensity (π : Measure (EuclideanSpace ℝ (Fin k)))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (r₀ : ℝ) (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    Prop where
  /-- Constitutive (vdV §10.2): the neighborhood of absolute continuity is nonempty. -/
  rad_pos : 0 < r₀
  /-- Constitutive (vdV §10.2): `f` is a density — wlog nonnegative. -/
  nonneg : ∀ θ, 0 ≤ f θ
  /-- Constitutive (vdV §10.2): `f` is a density — wlog Borel measurable
  (Radon–Nikodym supplies a measurable version). -/
  measurable : Measurable f
  /-- Constitutive (vdV §10.2): on `B(θ₀, r₀)` the prior has Lebesgue density `f`. -/
  restrict_eq : π.restrict (Metric.ball θ₀ r₀)
    = (volume.restrict (Metric.ball θ₀ r₀)).withDensity fun θ => ENNReal.ofReal (f θ)
  /-- Constitutive (vdV §10.2): the density is continuous at `θ₀`. -/
  continuousAt : ContinuousAt f θ₀
  /-- Constitutive (vdV §10.2): the density is positive at `θ₀`. -/
  pos : 0 < f θ₀

/-- Under the dominated-model hypothesis `hκ`, the classical product experiment
`P^n_θ = productMeasure M μ θ n` of the `AsymptoticStatistics` development is exactly the
iid sampling kernel `iidKernel κ n` evaluated at `θ`. -/
theorem productMeasure_eq_iidKernel_apply
    {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧}
    {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    productMeasure M μ θ n = iidKernel κ n θ := by
  rw [iidKernel_apply]
  exact congrArg Measure.pi (funext fun _ => (hκ θ).symm)

end StatLean.Bayesian
