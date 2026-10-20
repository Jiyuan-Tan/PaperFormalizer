module
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov
public import StatLean.AsymptoticStatistics.ForMathlib.SubsequenceLimit
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky
public import StatLean.AsymptoticStatistics.Experiment.GaussianShift
public import StatLean.AsymptoticStatistics.Experiment.RandomizedStatistic
public import StatLean.AsymptoticStatistics.Probability.ScoreCLT
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

/-!
# Theorem 7.10 — Asymptotic Representation (kernel form)

Given a parametric family differentiable in
quadratic mean at `θ₀` with score `ℓ_{θ₀}` and non-singular Fisher information `J`, and an
`𝓨`-valued statistic `T_n` with `T_n ⇝ L_h` under each `P^n_{θ₀ + h/√n}`, there exists a
Markov kernel `κ` such that `L_h = N(h, J⁻¹) >>= κ` for every `h`.

The proof combines contiguity, the score CLT, the Gaussian shift family,
Prohorov tightness, the Urysohn subsequence principle, and `LAN_expansion_iii` from
Theorem 7.2. `LAN_representation_of_gaussianShift` states the result for an
abstract Gaussian-shift family; `LAN_representation` specializes it to the canonical
multivariate Gaussian experiment.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics
namespace AsymptoticRepresentation

variable {k d : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ## Setup: notation shortcuts for this chapter

We fix the parameter space `Θ = EuclideanSpace ℝ (Fin k)` and the statistic's target
space `𝓨 = EuclideanSpace ℝ (Fin d)`. The `abbrev` keeps the full Mathlib typeclass
structure available while keeping signatures readable. -/

/-- Parameter space: finite-dimensional Euclidean. -/
abbrev Θ (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-- Target space of the statistic. -/
abbrev 𝓨 (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- `n`-fold product measure `P^n_θ` of `μ.withDensity (density θ)`. Each factor is the
probability measure associated to density `p_θ`. -/
noncomputable def productMeasure
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) (θ : Θ k) (n : ℕ) :
    Measure (Fin n → 𝓧) :=
  Measure.pi (fun _ => μ.withDensity fun x => ENNReal.ofReal (M.density θ x))

/-- **`productMeasure M μ θ n` is a probability measure**, given that `M` is a PDF
family (normalisation + integrability). Derives the typeclass instance from
`IsPDFOf` + `density_nonneg`. -/
theorem productMeasure_isProbabilityMeasure
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (hPDF : IsPDFOf M μ) (θ : Θ k) (n : ℕ) :
    IsProbabilityMeasure (productMeasure M μ θ n) := by
  haveI : IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ x)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ)
        (Filter.Eventually.of_forall (M.density_nonneg θ)),
      hPDF.density_integral_eq_one θ, ENNReal.ofReal_one]
  unfold productMeasure
  infer_instance

/-- Normalised score sum `Δ_n(ω) = (1/√n) ∑_{i < n} ℓ(ω i)`, a map `(Fin n → 𝓧) → Θ k`. -/
noncomputable def scoreSum (ℓ : 𝓧 → Θ k) (n : ℕ) (ω : Fin n → 𝓧) : Θ k :=
  (Real.sqrt n)⁻¹ • ∑ i, ℓ (ω i)

/-- Log-likelihood ratio of the shifted family to the base, evaluated on a sample:
`L_{n, h}(ω) = ∑_{i<n} log (p_{θ₀ + h/√n}(ω i) / p_{θ₀}(ω i))`. -/
noncomputable def logLikelihood
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ : Θ k) (h : Θ k) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  ∑ i, Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) (ω i) / M.density θ₀ (ω i))

/-- Measurability of `logLikelihood`, from `ParametricFamily.density_meas`. -/
lemma logLikelihood_measurable
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) :
    Measurable (logLikelihood M θ₀ h n) := by
  unfold logLikelihood
  refine Finset.univ.measurable_sum (fun i _ => ?_)
  refine Measurable.log ?_
  exact ((M.density_meas _).comp (measurable_pi_apply i)).div
    ((M.density_meas _).comp (measurable_pi_apply i))

/-- **Single-factor likelihood-ratio identity**. At the `μ`-level, the tilted
measure `μ.withDensity p'` decomposes as the tilt of the base `μ.withDensity p`
by the ratio `exp(log(p'/p))`, provided `p` and `p'` have the **same support**
(μ-a.e.). This is the minimal hypothesis — there is no separate positivity
assumption, the case `p = p' = 0` discharges by direct computation
(both sides of the integrand are `0`). -/
private lemma withDensity_density_eq_withDensity_mul_exp_log_ratio
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k) (h : Θ k) (n : ℕ)
    (h_same_support : ∀ᵐ x ∂μ,
      (0 < M.density θ₀ x ↔ 0 < M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) :
    (μ.withDensity (fun x => ENNReal.ofReal (M.density θ₀ x))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (Real.log
          (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x / M.density θ₀ x))))
      = μ.withDensity
          (fun x => ENNReal.ofReal
            (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) := by
  have hp_meas : Measurable (fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    (M.density_meas θ₀).ennreal_ofReal
  have hratio_meas : Measurable (fun x : 𝓧 => ENNReal.ofReal (Real.exp (Real.log
      (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x / M.density θ₀ x)))) :=
    (((M.density_meas _).div (M.density_meas _)).log.exp).ennreal_ofReal
  rw [← withDensity_mul _ hp_meas hratio_meas]
  refine withDensity_congr_ae ?_
  filter_upwards [h_same_support] with x h_iff
  -- Case split on `p(x) > 0`: interior case uses the standard Taylor-log
  -- identity; boundary case `p = 0` forces `p' = 0` via `h_iff`, making both
  -- sides of the integrand equal to `0`.
  rcases (M.density_nonneg θ₀ x).lt_or_eq with hp_pos | hp_zero
  · -- Interior case: `p > 0` and (via `h_iff`) `p' > 0`.
    have hp'_pos : 0 < M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x := h_iff.mp hp_pos
    have hratio_pos : 0 < M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x / M.density θ₀ x :=
      div_pos hp'_pos hp_pos
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (M.density_nonneg θ₀ x),
      Real.exp_log hratio_pos]
    congr 1
    field_simp
  · -- Boundary case: `p = 0`. By `h_iff` contrapositive, `p' = 0` too;
    -- both sides of the integrand collapse to `0`.
    have hp_eq : M.density θ₀ x = 0 := hp_zero.symm
    have hp'_zero : M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0 := by
      by_contra h_ne
      have hp'_pos : 0 < M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x :=
        lt_of_le_of_ne (M.density_nonneg _ _) (Ne.symm h_ne)
      exact absurd (h_iff.mpr hp'_pos) (by rw [hp_eq]; exact lt_irrefl 0)
    rw [Pi.mul_apply, hp_eq, hp'_zero, ENNReal.ofReal_zero, zero_mul]

/-- **Log-likelihood withDensity identity** — the Step-4 bridge from Step 3.
Under ae-positive densities, `productMeasure M μ θ' n` is the Radon-Nikodym
tilt of `productMeasure M μ θ₀ n` by the log-likelihood-ratio exponential.

The proof applies `pi_withDensity_prod` to decompose the product tilt into a
product of per-coordinate tilts, then closes each factor via
`withDensity_density_eq_withDensity_mul_exp_log_ratio`. -/
theorem logLikelihood_is_log_ratio
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (h : Θ k) (n : ℕ)
    (hint_perturb :
      Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) μ)
    (h_same_support : ∀ᵐ x ∂μ,
      (0 < M.density θ₀ x ↔ 0 < M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) :
    productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n
      = (productMeasure M μ θ₀ n).withDensity
          (fun ω : Fin n → 𝓧 =>
            ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))) := by
  set θ' : Θ k := θ₀ + (Real.sqrt n)⁻¹ • h with hθ'_def
  set pEnn : 𝓧 → ℝ≥0∞ := fun x => ENNReal.ofReal (M.density θ₀ x) with hpEnn_def
  set fUnit : 𝓧 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (Real.log
      (M.density θ' x / M.density θ₀ x))) with hfUnit_def
  have hp_meas : Measurable pEnn := (M.density_meas θ₀).ennreal_ofReal
  have hfUnit_meas : Measurable fUnit :=
    (((M.density_meas _).div (M.density_meas _)).log.exp).ennreal_ofReal
  -- Rewrite the RHS integrand: ofReal(exp(∑ log r)) = ∏ ofReal(exp(log r)).
  have h_integrand :
      (fun ω : Fin n → 𝓧 =>
          ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω)))
        = fun ω : Fin n → 𝓧 => ∏ i, fUnit (ω i) := by
    funext ω
    unfold logLikelihood
    rw [Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [h_integrand]
  -- The single-factor identity upgrades to an equality of measures.
  have h_factor :
      (μ.withDensity pEnn).withDensity fUnit
        = μ.withDensity (fun x => ENNReal.ofReal (M.density θ' x)) :=
    withDensity_density_eq_withDensity_mul_exp_log_ratio M μ θ₀ h n h_same_support
  -- Register sigma-finiteness of the per-factor tilt (needed by
  -- `pi_withDensity_prod`) using that it equals `μ.withDensity (ENNReal.ofReal ∘ p')`,
  -- which is a finite measure by `hint_perturb`.
  haveI : IsFiniteMeasure ((μ.withDensity pEnn).withDensity fUnit) := by
    rw [h_factor]
    exact isFiniteMeasure_withDensity_ofReal hint_perturb.hasFiniteIntegral
  -- Unfold `productMeasure` and invoke `pi_withDensity_prod` in reverse.
  change Measure.pi (fun _ : Fin n => _)
    = (Measure.pi (fun _ : Fin n => μ.withDensity pEnn)).withDensity
        (fun ω => ∏ i, fUnit (ω i))
  rw [pi_withDensity_prod (fun _ : Fin n => hfUnit_meas)]
  -- Both sides are product measures; compare their factors.
  congr 1
  funext _
  exact h_factor.symm

/-! ## Step 1 — Score CLT under `P^n_{θ₀}`

The normalized score sum `Δ_n` is asymptotically `N(0, J)` under the base measure
`P^n_{θ₀}`. The derivation chains:
* `LANExpansion.score_mean_zero` (zero mean under `P_θ₀`),
* `DQM.dqm_fisher_integrable` (finite second moment ⇒ `L²`),
* the multivariate CLT `ScoreCLT.clt_finDim` (Cramér–Wold via Lévy continuity),
* an iid-joint-law bridge `productMeasure = P.map (ω ↦ (fun i ↦ X i ω))` to convert from
  the abstract-Ω setup `clt_finDim` expects to the `productMeasure` setup used here.

The theorem `scoreSum_weakly_converges` combines these ingredients. -/

theorem score_clt_local
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (_hℓ : Measurable ℓ)
    (_hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (_hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (h_clt_output :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
        (ProbabilityTheory.multivariateGaussian (0 : Θ k) J)) :
    WeakConverges (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) :=
  h_clt_output

/-- **Pushforward identity**: The law of the abstract score sum `(√n)⁻¹ ∑ ℓ(ω i)`
under the Kolmogorov extension `infinitePi (const ν)` on `ℕ → 𝓧` equals the law of
`scoreSum ℓ n` under `productMeasure M μ θ₀ n` on `Fin n → 𝓧`.

The equality transports the abstract `clt_finDim` expression to the finite-product
score sum. It factors the restriction-map transport
(`pi_const_eq_infinitePi_map`) through the re-indexing identity
`scoreSum ℓ n ∘ restrict_n = abstract_sum n`. -/
lemma scoreSum_pushforward_eq
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ) (n : ℕ) :
    (productMeasure M μ θ₀ n).map (scoreSum ℓ n)
      = (Measure.infinitePi
            (fun _ : ℕ => μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))).map
          (fun ω : ℕ → 𝓧 => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, ℓ (ω i)) := by
  -- `ν := μ.withDensity (density θ₀)` is a probability measure (`h_one` + `hint`).
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) with hν_def
  haveI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (M.density_nonneg θ₀)),
      h_one, ENNReal.ofReal_one]
  -- The abstract sum `(√n)⁻¹ ∑ ℓ(ω i)` factors through the `Fin n`-restriction as
  -- `scoreSum ℓ n ∘ restrict_n`.
  have h_restrict_meas :
      Measurable (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have h_factor :
      (fun ω : ℕ → 𝓧 => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, ℓ (ω i))
        = scoreSum ℓ n ∘ (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) := by
    funext ω
    simp only [Function.comp_apply, scoreSum]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i => ℓ (ω i)) n).symm
  have h_scoreSum_meas : Measurable (scoreSum ℓ n) := by
    unfold scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  rw [h_factor, ← Measure.map_map h_scoreSum_meas h_restrict_meas,
    ← AsymptoticStatistics.pi_const_eq_infinitePi_map ν n]
  rfl

/-- Transport of the abstract `(ℕ → 𝓧, infinitePi)` central limit theorem to
`productMeasure`, using `scoreSum_pushforward_eq`. -/
lemma scoreSum_weakly_converges_of_abstract
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (h_abstract_clt :
      WeakConverges (fun n =>
        (Measure.infinitePi
            (fun _ : ℕ => μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))).map
          (fun ω : ℕ → 𝓧 => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, ℓ (ω i)))
        (ProbabilityTheory.multivariateGaussian (0 : Θ k) J)) :
    WeakConverges (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) := by
  have h_eq : ∀ n, (productMeasure M μ θ₀ n).map (scoreSum ℓ n)
      = (Measure.infinitePi
            (fun _ : ℕ => μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))).map
          (fun ω : ℕ → 𝓧 => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, ℓ (ω i)) := fun n =>
    scoreSum_pushforward_eq M μ θ₀ h_one hint ℓ hℓ n
  intro f
  simp_rw [h_eq]
  exact h_abstract_clt f

/-- **`scoreSum` weak convergence under `productMeasure`** — assembly of Step 1.

Applies the abstract multivariate CLT `ScoreCLT.clt_finDim` to the Kolmogorov-extension
iid setup on `(ℕ → 𝓧, Measure.infinitePi (const ν))` with `ν := μ.withDensity (density θ₀)`,
then transports the conclusion to `productMeasure` via
`scoreSum_weakly_converges_of_abstract`.

The four `clt_finDim` iid hypotheses are discharged internally:
* **iid / ident**: `ProbabilityTheory.iIndepFun_infinitePi` + `Measure.infinitePi_map_eval`.
* **Zero mean**: `integral_map` + `integral_withDensity_eq_integral_toReal_smul` to translate
  `∫ ⟪u, Y 0 ω⟫ dP` into `∫ ⟪u, ℓ x⟫ * density θ₀ x dμ`; then
  `AsymptoticStatistics.score_mean_zero` (which needs `dqm_fisher_integrable` and
  `dqm_residual_eventually_memLp` from `DQM/Properties.lean`).
* **Covariance**: same translation, then the definition of `fisherInformation` plus `hJ`.
* **L²**: `MemLp (Y 0) 2 P` via `memLp_map_measure_iff` + `MemLp ℓ 2 ν`; the latter reduces
  via `memLp_two_iff_integrable_sq_norm` + `integrable_withDensity_iff` to integrability of
  `‖ℓ x‖² * density θ₀ x`, which decomposes coordinate-wise using
  `EuclideanSpace.real_norm_sq_eq` + `EuclideanSpace.inner_single_left` and sums the
  `dqm_fisher_integrable` bounds over the standard basis.
-/
theorem scoreSum_weakly_converges
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k)
    (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ k, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ k, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_psd : J.PosSemidef)
    (hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫) :
    WeakConverges (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) := by
  classical
  -- Setup ν := μ.withDensity (density θ₀).
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) with hν_def
  haveI hν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (M.density_nonneg θ₀)),
      h_one, ENNReal.ofReal_one]
  -- Kolmogorov extension P and coordinate projections Y.
  let P : Measure (ℕ → 𝓧) := Measure.infinitePi (fun _ : ℕ => ν)
  haveI hP_prob : IsProbabilityMeasure P := inferInstance
  let Y : ℕ → (ℕ → 𝓧) → Θ k := fun i ω => ℓ (ω i)
  have hY_meas : ∀ i, Measurable (Y i) := fun i => hℓ.comp (measurable_pi_apply i)
  -- iid + ident for Y.
  have h_coord_iid : ProbabilityTheory.iIndepFun (fun i (ω : ℕ → 𝓧) => ω i) P :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun (_ : ℕ) (x : 𝓧) => x)
      (fun _ => measurable_id)
  have hY_iid : ProbabilityTheory.iIndepFun Y P :=
    h_coord_iid.comp (g := fun _ => ℓ) (fun _ => hℓ)
  have hX_law : ∀ i, Measure.map (fun ω : ℕ → 𝓧 => ω i) P = ν := fun i =>
    MeasureTheory.Measure.infinitePi_map_eval _ i
  have hY_law : ∀ i, Measure.map (Y i) P = ν.map ℓ := fun i => by
    change Measure.map ((fun x => ℓ x) ∘ (fun ω : ℕ → 𝓧 => ω i)) P = _
    rw [← Measure.map_map hℓ (measurable_pi_apply i), hX_law i]
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) P P := fun i =>
    ⟨(hY_meas i).aemeasurable, (hY_meas 0).aemeasurable, by rw [hY_law i, hY_law 0]⟩
  -- Fisher / score-mean regularity from DQM (plug-in hypotheses for score_mean_zero).
  have h_Fisher : ∀ u : Θ k,
      Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ :=
    fun u => dqm_fisher_integrable M μ θ₀ ℓ hint hDQM u (fun t => hint_perturb t u)
  have h_fminus_memLp : ∀ u : Θ k, ∀ᶠ t in 𝓝[≠] (0 : ℝ), MemLp (fun x =>
        t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
          - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ :=
    fun u => dqm_residual_eventually_memLp M μ θ₀ ℓ hDQM u
  have h_score_mean : ∀ u : Θ k, ∫ x, ⟪u, ℓ x⟫ * M.density θ₀ x ∂μ = 0 := fun u =>
    AsymptoticStatistics.Score.score_mean_zero M μ θ₀ ℓ hℓ h_one hint h_one_perturb
      hint_perturb hDQM (h_Fisher u) (h_fminus_memLp u)
  -- Helper: measurable integrand `⟪u, ℓ (·0)⟫` coming from integral_map.
  have h_ASM_lin : ∀ u : Θ k, AEStronglyMeasurable (fun x : 𝓧 => ⟪u, ℓ x⟫) ν :=
    fun u => (Measurable.const_inner (c := u) hℓ).aestronglyMeasurable
  have h_ASM_cov : ∀ u v : Θ k,
      AEStronglyMeasurable (fun x : 𝓧 => ⟪u, ℓ x⟫ * ⟪v, ℓ x⟫) ν := fun u v =>
    ((Measurable.const_inner (c := u) hℓ).mul
      (Measurable.const_inner (c := v) hℓ)).aestronglyMeasurable
  -- Zero mean of Y 0 under P.
  have h_zero_mean_P : ∀ u : Θ k, ∫ ω, ⟪u, Y 0 ω⟫ ∂P = 0 := by
    intro u
    have h1 : ∫ ω, ⟪u, Y 0 ω⟫ ∂P = ∫ x, ⟪u, ℓ x⟫ ∂ν := by
      have h_int : ∫ y, ⟪u, ℓ y⟫ ∂(P.map (fun ω : ℕ → 𝓧 => ω 0))
          = ∫ ω, ⟪u, ℓ (ω 0)⟫ ∂P := by
        refine MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable ?_
        rw [hX_law 0]
        exact (Measurable.const_inner (c := u) hℓ).aestronglyMeasurable
      rw [hX_law 0] at h_int
      exact h_int.symm
    have h2 : ∫ x, ⟪u, ℓ x⟫ ∂ν = ∫ x, ⟪u, ℓ x⟫ * M.density θ₀ x ∂μ := by
      rw [hν_def,
        integral_withDensity_eq_integral_toReal_smul (M.density_meas θ₀).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), smul_eq_mul]
      ring
    rw [h1, h2]
    exact h_score_mean u
  -- Covariance of Y 0 under P: matches fisherInformation = ⟨u, J v⟩_Mat.
  have h_cov_P : ∀ u v : Θ k,
      ∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P = u.ofLp ⬝ᵥ J.mulVec v.ofLp := by
    intro u v
    have h1 : ∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P
        = ∫ x, ⟪u, ℓ x⟫ * ⟪v, ℓ x⟫ ∂ν := by
      have h_int : ∫ y, ⟪u, ℓ y⟫ * ⟪v, ℓ y⟫ ∂(P.map (fun ω : ℕ → 𝓧 => ω 0))
          = ∫ ω, ⟪u, ℓ (ω 0)⟫ * ⟪v, ℓ (ω 0)⟫ ∂P := by
        refine MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable ?_
        rw [hX_law 0]
        exact ((Measurable.const_inner (c := u) hℓ).mul
          (Measurable.const_inner (c := v) hℓ)).aestronglyMeasurable
      rw [hX_law 0] at h_int
      exact h_int.symm
    have h2 : ∫ x, ⟪u, ℓ x⟫ * ⟪v, ℓ x⟫ ∂ν
        = ∫ x, ⟪u, ℓ x⟫ * ⟪v, ℓ x⟫ * M.density θ₀ x ∂μ := by
      rw [hν_def,
        integral_withDensity_eq_integral_toReal_smul (M.density_meas θ₀).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), smul_eq_mul]
      ring
    rw [h1, h2]
    -- `∫ ⟪u, ℓ⟫ * ⟪v, ℓ⟫ * density ∂μ = fisherInformation M μ θ₀ ℓ u v` (definition).
    change fisherInformation M μ θ₀ ℓ u v = _
    rw [hJ u v]
    -- Bridge: `⟪u, (equiv).symm (J.mulVec (equiv v))⟫ = u.ofLp ⬝ᵥ J.mulVec v.ofLp`.
    simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply,
      ]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (J.mulVec v.ofLp) i * u.ofLp i = u.ofLp i * (J.mulVec v.ofLp) i
    ring
  -- L² memberness of ℓ under ν: via coordinate-wise fisher integrability.
  have hL2_ℓ_ν : MemLp ℓ 2 ν := by
    rw [memLp_two_iff_integrable_sq_norm hℓ.aestronglyMeasurable]
    rw [hν_def, MeasureTheory.integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top |>.lt_top)]
    -- Goal: Integrable (fun x => ‖ℓ x‖^2 * (ENNReal.ofReal (density θ₀ x)).toReal) μ
    have h_inner_eq : ∀ (x : 𝓧) (i : Fin k),
        ⟪(EuclideanSpace.single i (1 : ℝ) : Θ k), ℓ x⟫ = (ℓ x).ofLp i := by
      intro x i
      have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) (ℓ x)
      simpa using h
    have h_rewrite : (fun x => ‖ℓ x‖ ^ 2 * (ENNReal.ofReal (M.density θ₀ x)).toReal)
        =ᵐ[μ] fun x => ∑ i : Fin k,
          ⟪(EuclideanSpace.single i (1 : ℝ) : Θ k), ℓ x⟫ ^ 2 * M.density θ₀ x := by
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x),
        EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_inner_eq x i]
    refine (integrable_congr h_rewrite).mpr ?_
    exact MeasureTheory.integrable_finset_sum _
      (fun i _ => h_Fisher (EuclideanSpace.single i (1 : ℝ)))
  -- L² memberness of Y 0 under P, via `memLp_map_measure_iff` + `hX_law 0`.
  have h_L2_P : MemLp (Y 0) 2 P := by
    change MemLp (ℓ ∘ (fun ω : ℕ → 𝓧 => ω 0)) 2 P
    have h_meas_eq : (P.map (fun ω : ℕ → 𝓧 => ω 0)) = ν := hX_law 0
    refine
      (MeasureTheory.memLp_map_measure_iff (?_ : AEStronglyMeasurable ℓ _)
        (measurable_pi_apply 0).aemeasurable).mp ?_
    · rw [h_meas_eq]; exact hℓ.aestronglyMeasurable
    · rw [h_meas_eq]; exact hL2_ℓ_ν
  -- Apply `clt_finDim` to the abstract iid setup.
  have h_abs_clt := ScoreCLT.clt_finDim P Y hY_meas hY_iid hident h_zero_mean_P
    J hJ_psd h_cov_P h_L2_P
  -- Transport to productMeasure form.
  exact scoreSum_weakly_converges_of_abstract M μ θ₀ h_one hint ℓ hℓ J h_abs_clt

/-! ## Step 2 — Marginal tightness + Prohorov subsequence

Given that `T_n` is tight at `h = 0` and `Δ_n` is tight (from Step 1), the joint
sequence `(T_n, Δ_n)` is tight. Prohorov then extracts a weakly convergent
subsequence with a joint limit `(S, Δ)`; the second marginal is uniquely `N(0, J)`
by Step 1. -/

theorem joint_weak_subsequence
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    [∀ n, IsProbabilityMeasure (productMeasure M μ θ₀ n)]
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L_zero : Measure (𝓨 d)) [IsProbabilityMeasure L_zero]
    (hT_tight_at_zero :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map (T n)) L_zero)
    (ν : Measure (Θ k)) [IsProbabilityMeasure ν]
    (hΔ_tight :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n)) ν) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (π : Measure (𝓨 d × Θ k)),
      IsProbabilityMeasure π ∧
      WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, scoreSum ℓ (φ k_idx) ω))) π := by
  -- Measurability of `scoreSum` as a function of the product coordinates.
  have hΔ_meas : ∀ n, Measurable (scoreSum ℓ n) := by
    intro n
    unfold scoreSum
    have h_sum : Measurable (fun ω : Fin n → 𝓧 => ∑ i, ℓ (ω i)) :=
      Finset.univ.measurable_sum (fun i _ => hℓ.comp (measurable_pi_apply i))
    exact h_sum.const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- Measurability of the joint pushforward function.
  have h_joint_meas : ∀ n,
      Measurable (fun ω : Fin n → 𝓧 => (T n ω, scoreSum ℓ n ω)) :=
    fun n => (hT_meas n).prodMk (hΔ_meas n)
  -- Short names for the joint and marginal pushforward sequences.
  set joint : ℕ → Measure (𝓨 d × Θ k) := fun n =>
    (productMeasure M μ θ₀ n).map (fun ω => (T n ω, scoreSum ℓ n ω)) with hjoint_def
  set Tseq : ℕ → Measure (𝓨 d) := fun n => (productMeasure M μ θ₀ n).map (T n)
    with hTseq_def
  set Δseq : ℕ → Measure (Θ k) := fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n)
    with hΔseq_def
  -- The joint pushforward is a probability measure.
  haveI h_joint_prob : ∀ n, IsProbabilityMeasure (joint n) := fun n =>
    Measure.isProbabilityMeasure_map (h_joint_meas n).aemeasurable
  haveI h_T_prob : ∀ n, IsProbabilityMeasure (Tseq n) := fun n =>
    Measure.isProbabilityMeasure_map (hT_meas n).aemeasurable
  haveI h_Δ_prob : ∀ n, IsProbabilityMeasure (Δseq n) := fun n =>
    Measure.isProbabilityMeasure_map (hΔ_meas n).aemeasurable
  -- Each marginal of joint equals the respective `T` / `Δ` pushforward.
  have h_marg_fst : ∀ n, (joint n).map Prod.fst = Tseq n := by
    intro n
    simp only [hjoint_def, hTseq_def, Measure.map_map measurable_fst (h_joint_meas n)]
    rfl
  have h_marg_snd : ∀ n, (joint n).map Prod.snd = Δseq n := by
    intro n
    simp only [hjoint_def, hΔseq_def, Measure.map_map measurable_snd (h_joint_meas n)]
    rfl
  -- Each marginal sequence is tight (weak convergence ⇒ tight).
  have hT_range_tight : IsTightMeasureSet (Set.range Tseq) :=
    Prohorov.weakConverges_range_tight _ _ hT_tight_at_zero
  have hΔ_range_tight : IsTightMeasureSet (Set.range Δseq) :=
    Prohorov.weakConverges_range_tight _ _ hΔ_tight
  -- Images of the joint range under marginal projections equal the `T` / `Δ` ranges.
  have h_fst_image :
      (fun ρ : Measure (𝓨 d × Θ k) => ρ.map Prod.fst) '' (Set.range joint)
        = Set.range Tseq := by
    ext ρ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (h_marg_fst n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨joint n, ⟨n, rfl⟩, h_marg_fst n⟩
  have h_snd_image :
      (fun ρ : Measure (𝓨 d × Θ k) => ρ.map Prod.snd) '' (Set.range joint)
        = Set.range Δseq := by
    ext ρ
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (h_marg_snd n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨joint n, ⟨n, rfl⟩, h_marg_snd n⟩
  -- Joint tightness.
  have h_joint_tight : IsTightMeasureSet (Set.range joint) :=
    Prohorov.tight_prod_of_tight_marginals _
      (h_fst_image ▸ hT_range_tight)
      (h_snd_image ▸ hΔ_range_tight)
  -- Extract weakly convergent subsequence via Prohorov.
  obtain ⟨φ, hφ_mono, π, hπ_prob, h_conv⟩ :=
    Prohorov.extract_weak_subseq joint h_joint_tight
  exact ⟨φ, hφ_mono, π, hπ_prob, h_conv⟩

/-- **Joint weak convergence with the score sum, plus second-marginal identification.**

The theorem combines three facts:

1. The score CLT under `P^n_{θ₀}` (via `scoreSum_weakly_converges`) gives
   `Δ_n ⇝ multivariateGaussian 0 J`.
2. Combined with `hT_weak_0`, joint tightness + Prohorov extracts a subsequence
   `φ` along which `(T_n, Δ_n) ⇝ π`.
3. The second marginal of `π` is identified as `multivariateGaussian 0 J` via
   `WeakConverges.snd_eq`.

Thus the extracted joint limit includes its Gaussian second-marginal identity. -/
theorem joint_weak_conv_with_scoreSum
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L0 : Measure (𝓨 d)) [IsProbabilityMeasure L0]
    (hT_weak_0 : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (T n)) L0)
    (hPDF : IsPDFOf M μ) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (π : Measure (𝓨 d × Θ k)),
      IsProbabilityMeasure π
      ∧ WeakConverges (fun k => (productMeasure M μ θ₀ (φ k)).map
            (fun ω => (T (φ k) ω, scoreSum ℓ (φ k) ω))) π
      ∧ π.map Prod.snd = ProbabilityTheory.multivariateGaussian (0 : Θ k) J := by
  -- Derive probability-measure instance from `hPDF`.
  haveI : ∀ n, IsProbabilityMeasure (productMeasure M μ θ₀ n) :=
    fun n => productMeasure_isProbabilityMeasure M μ hPDF θ₀ n
  -- Unpack `hPDF` to per-parameter regularity.
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : Θ k,
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : Θ k,
      Integrable (M.density (θ₀ + t • u)) μ :=
    fun t u => hPDF.density_integrable (θ₀ + t • u)
  -- Step 1: score CLT under `P^n_{θ₀}`.
  have hScoreCLT : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb
      hDQM J hJ_pd.posSemidef hJ
  -- Weak convergence of the score laws implies tightness.
  have h_Δ_tight := score_clt_local M μ θ₀ ℓ hℓ hDQM J hJ hScoreCLT
  -- Step 2: extract joint subsequence via Prohorov.
  obtain ⟨φ, hφ_mono, π, hπ_prob, h_joint⟩ :=
    joint_weak_subsequence M μ θ₀ ℓ hℓ T hT_meas L0 hT_weak_0
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) h_Δ_tight
  -- Step 3: identify the second marginal of `π`.
  have h_Δ_meas : ∀ n, Measurable (scoreSum ℓ n) := by
    intro n
    unfold scoreSum
    have h_sum : Measurable (fun ω : Fin n → 𝓧 => ∑ i, ℓ (ω i)) :=
      Finset.univ.measurable_sum (fun i _ => hℓ.comp (measurable_pi_apply i))
    exact h_sum.const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have h_π_snd : π.map Prod.snd =
      ProbabilityTheory.multivariateGaussian (0 : Θ k) J := by
    have h_marg : ∀ k_idx,
        ((productMeasure M μ θ₀ (φ k_idx)).map
            (fun ω => (T (φ k_idx) ω, scoreSum ℓ (φ k_idx) ω))).map Prod.snd
          = (productMeasure M μ θ₀ (φ k_idx)).map (scoreSum ℓ (φ k_idx)) := by
      intro k_idx
      rw [Measure.map_map measurable_snd
        ((hT_meas (φ k_idx)).prodMk (h_Δ_meas (φ k_idx)))]
      rfl
    have hν : WeakConverges
        (fun k_idx => ((productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, scoreSum ℓ (φ k_idx) ω))).map Prod.snd)
        (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) := by
      simp_rw [h_marg]
      exact hScoreCLT.comp hφ_mono
    exact WeakConverges.snd_eq h_joint hν
  exact ⟨φ, hφ_mono, π, hπ_prob, h_joint, h_π_snd⟩

/-! ## Step 3 — Joint weak convergence with log-likelihood ratio

By `LANExpansion.LAN_expansion_iii` the log-likelihood ratio decomposes as
`⟨h, Δ_n⟩ - ½ ⟨h, J h⟩ + o_P(1)`. Combined with Step 2's joint weak convergence of
`(T_n, Δ_n)` along a subsequence, and Slutsky to absorb the `o_P(1)`, we get
joint weak convergence of `(T_n, L_{n,h})` under `P^n_{θ₀}`.

The proof factors into three pieces:
1. Apply `WeakConverges.map` with the continuous affine
   `tilt_map (s, δ) := (s, ⟨h, δ⟩ - ½ ⟨h, J h⟩)` to the Step-2 joint convergence.
   This yields `(T_n, g(Δ_n)) ⇝ π.map tilt_map`.
2. The Slutsky perturbation: `logLikelihood_n = g(Δ_n) + o_P(1)` (by
   `LAN_expansion_iii`), and replacing the second coordinate by the log-likelihood
   leaves the weak limit unchanged. This is encoded as the hypothesis
   `h_slutsky_bridge`.
3. The final joint weak convergence follows. -/

theorem joint_weak_with_logLikelihood
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (_hℓ : Measurable ℓ)
    (_hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (_hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (_hT_meas : ∀ n, Measurable (T n))
    (_h : Θ k)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (h_subseq_joint :
      WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, scoreSum ℓ (φ k_idx) ω))) π)
    -- Slutsky perturbation: replacing the second coordinate `⟨_h, Δ_n⟩ - ½⟨_h, J _h⟩`
    -- (the output of piece (1), via the affine `tilt_map`) by `logLikelihood_n` leaves
    -- the joint weak limit unchanged, because their difference is `o_P(1)` under
    -- `P^n_{θ₀}` by the LAN expansion. Encoded as an implication: given the linearised
    -- joint weak convergence, the log-likelihood joint weakly converges to the same
    -- tilt of `π`.
    (h_slutsky_bridge :
      WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω =>
            (T (φ k_idx) ω,
             ⟪_h, scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
               ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫)))
        (π.map (fun p : 𝓨 d × Θ k =>
          (p.1, ⟪_h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫))) →
      WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, logLikelihood M θ₀ _h (φ k_idx) ω)))
        (π.map (fun p =>
          (p.1, ⟪_h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫)))) :
    -- Conclusion: along the same `φ`, `(T_{φ_k}, logLikelihood _{φ_k, h})` converges
    -- weakly under `P^{φ_k}_{θ₀}` to the pushforward of `π` by the affine map
    -- `(s, δ) ↦ (s, ⟨_h, δ⟩ - ½ ⟨_h, J _h⟩)`.
    WeakConverges
      (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
        (fun ω => (T (φ k_idx) ω, logLikelihood M θ₀ _h (φ k_idx) ω)))
      (π.map (fun p =>
        (p.1, ⟪_h, p.2⟫ - (1 / 2 : ℝ) *
          ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫))) := by
  -- Piece (1): apply the generic continuous-mapping theorem with the affine tilt.
  let tilt_map : 𝓨 d × Θ k → 𝓨 d × ℝ := fun p =>
    (p.1, ⟪_h, p.2⟫ - (1 / 2 : ℝ) *
      ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫)
  have htilt_cont : Continuous tilt_map :=
    continuous_fst.prodMk
      ((continuous_const.inner continuous_snd).sub continuous_const)
  have htilt_meas : Measurable tilt_map := htilt_cont.measurable
  have h_cm := h_subseq_joint.map htilt_cont htilt_meas
  -- `h_cm`'s push-forward measure is `(P_{φ k}.map (T, Δ)).map tilt_map`, which by
  -- `Measure.map_map` equals `P_{φ k}.map (tilt_map ∘ (T, Δ))` — exactly the shape
  -- the Slutsky bridge expects on its LHS.
  have hΔ_meas : ∀ n, Measurable (scoreSum ℓ n) := by
    intro n
    unfold scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => _hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have h_linear_joint :
      WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω =>
            (T (φ k_idx) ω,
             ⟪_h, scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
               ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫)))
        (π.map tilt_map) := by
    intro f
    have h_fun_eq : ∀ k_idx,
        ((productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, scoreSum ℓ (φ k_idx) ω))).map tilt_map =
        (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω =>
            (T (φ k_idx) ω,
             ⟪_h, scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
               ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫)) := by
      intro k_idx
      rw [MeasureTheory.Measure.map_map htilt_meas
        ((_hT_meas (φ k_idx)).prodMk (hΔ_meas (φ k_idx)))]
      rfl
    have := h_cm f
    simp_rw [h_fun_eq] at this
    exact this
  -- Piece (2): apply the Slutsky perturbation hypothesis.
  exact h_slutsky_bridge h_linear_joint

/-- **Slutsky theorem for the LAN residual.** Given that the LAN residual
`logLikelihood - linearized` vanishes
in probability under `productMeasure`, the linearised joint weak convergence lifts
to the log-likelihood joint weak convergence. -/
theorem slutsky_bridge_of_lanResidual
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (h : Θ k)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (φ : ℕ → ℕ)
    (hLogLik_meas : ∀ n, Measurable (logLikelihood M θ₀ h n))
    (h_lanResidual : ∀ ε > 0,
      Tendsto (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).real
        {ω | ε ≤ |logLikelihood M θ₀ h (φ k_idx) ω
                 - (⟪h, scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|})
        atTop (𝓝 0)) :
    WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω =>
            (T (φ k_idx) ω,
             ⟪h, scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
               ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)))
        (π.map (fun p : 𝓨 d × Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) →
    WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, logLikelihood M θ₀ h (φ k_idx) ω)))
        (π.map (fun p : 𝓨 d × Θ k =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) := by
  intro h_linear_joint
  haveI : IsProbabilityMeasure (π.map (fun p : 𝓨 d × Θ k =>
      (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
        ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) := by
    refine Measure.isProbabilityMeasure_map ?_
    fun_prop
  have hΔ_meas : ∀ n, Measurable (scoreSum ℓ n) := by
    intro n
    unfold scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- Package the two random-variable sequences `X_n = (T, linearised)` and
  -- `Y_n = (T, logLik)` as pushforward targets in `𝓨 d × ℝ`.
  set X : ∀ n : ℕ, (Fin (φ n) → 𝓧) → 𝓨 d × ℝ := fun n ω =>
    (T (φ n) ω,
     ⟪h, scoreSum ℓ (φ n) ω⟫ - (1 / 2 : ℝ) *
       ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫) with hX_def
  set Y : ∀ n : ℕ, (Fin (φ n) → 𝓧) → 𝓨 d × ℝ := fun n ω =>
    (T (φ n) ω, logLikelihood M θ₀ h (φ n) ω) with hY_def
  have hX_meas : ∀ n, Measurable (X n) := fun n =>
    (hT_meas _).prodMk ((Measurable.const_inner (c := h) (hΔ_meas _)).sub measurable_const)
  have hY_meas : ∀ n, Measurable (Y n) := fun n =>
    (hT_meas _).prodMk (hLogLik_meas _)
  -- Apply Slutsky's theorem.
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => (hX_meas n).aemeasurable) (fun n => (hY_meas n).aemeasurable)
    h_linear_joint ?_
  -- Distance condition: the product-metric distance reduces to `|residual|`.
  intro ε hε
  convert h_lanResidual ε hε using 3 with k_idx
  ext ω
  change ε ≤ dist (X k_idx ω) (Y k_idx ω) ↔ _
  have h_dist_eq : dist (X k_idx ω) (Y k_idx ω)
      = |logLikelihood M θ₀ h (φ k_idx) ω
         - (⟪h, scoreSum ℓ (φ k_idx) ω⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)| := by
    simp only [hX_def, hY_def, Prod.dist_eq, dist_self, Real.dist_eq]
    rw [max_eq_right (abs_nonneg _), abs_sub_comm]
  rw [h_dist_eq]
  rfl

/-- **LAN residual vanishes in `productMeasure` probability**.

Applies `LANExpansion.LAN_expansion_iii` on the abstract iid space
`(ℕ → 𝓧, Measure.infinitePi (const ν))` (with `ν = μ.withDensity (density θ₀)` and
coordinate projections as the iid sample), then transports the resulting
`TendstoInMeasure` to `productMeasure M μ θ₀ n` via the restriction map
`(ℕ → 𝓧) → (Fin n → 𝓧)`.

This is exactly the hypothesis shape consumed by `slutsky_bridge_of_lanResidual`
(after composition with a subsequence `φ`). -/
theorem lanResidual_tendsto_productMeasure
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k)
    [∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n)]
    (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (h_one : ∫ x, M.density θ₀ x ∂μ = 1)
    (hint : Integrable (M.density θ₀) μ)
    (h_one_perturb : ∀ t : ℝ, ∀ u : Θ k, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ k, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (h : Θ k) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLikelihood M θ₀ h n ω
                 - (⟪h, scoreSum ℓ n ω⟫ - (1/2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|})
        atTop (𝓝 0) := by
  -- Abstract iid setup: Ω = ℕ → 𝓧, P = infinitePi (const ν), X i = coordinate i.
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) with hν_def
  haveI hν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (M.density_nonneg θ₀)),
      h_one, ENNReal.ofReal_one]
  let P : Measure (ℕ → 𝓧) := Measure.infinitePi (fun _ : ℕ => ν)
  haveI hP_prob : IsProbabilityMeasure P := inferInstance
  let X : ℕ → (ℕ → 𝓧) → 𝓧 := fun i ω => ω i
  have hX_meas : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  -- Coordinate projections are jointly independent (hence pairwise).
  have hiid : ProbabilityTheory.iIndepFun X P :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun (_ : ℕ) (x : 𝓧) => x)
      (fun _ => measurable_id)
  have hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) P :=
    fun _ _ hij => hiid.indepFun hij
  -- Each coordinate has law ν.
  have hX_law : ∀ i, Measure.map (X i) P = ν := fun i =>
    MeasureTheory.Measure.infinitePi_map_eval _ i
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P := by
    intro i
    refine ⟨(hX_meas i).aemeasurable, (hX_meas 0).aemeasurable, ?_⟩
    rw [hX_law i, hX_law 0]
  have hlaw : Measure.map (X 0) P =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) := hX_law 0
  -- Invoke LAN_expansion_iii with the constant sequence `h_n = h`.
  have hconv : Tendsto (fun _ : ℕ => h) atTop (𝓝 h) := tendsto_const_nhds
  have hLAN := LANExpansion.LAN_expansion_iii P M μ θ₀ ℓ hℓ h_one hint
    h_one_perturb hint_perturb hDQM h (fun _ => h) hconv
    X hX_meas hindep hident hlaw
  -- The conclusion `TendstoInMeasure P residual_abs atTop 0` gives, via the norm
  -- form, a real-valued tendsto of `P {ω | ε ≤ |residual_abs n ω|}` to 0 in ℝ≥0∞.
  rw [MeasureTheory.tendstoInMeasure_iff_norm] at hLAN
  intro ε hε
  have hLAN_ε := hLAN ε hε
  -- Transport each set measure to `productMeasure` via the restriction map
  -- `restrictN n : (ℕ → 𝓧) → (Fin n → 𝓧)`, defined inline because `n` is universally
  -- quantified in each subsequent step.
  have h_restrict_meas : ∀ n, Measurable (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) :=
    fun n => measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  -- Abbreviation for the scalar `⟨h, J h⟩_Mat`.
  set J_term : ℝ :=
    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ with hJ_term_def
  have hJ_fisher : fisherInformation M μ θ₀ ℓ h h = J_term := hJ h h
  -- Scalar product: ⟪h, (√n)⁻¹ • ∑ i, ℓ(ω i)⟫ = (√n)⁻¹ * ∑ i, ⟪h, ℓ(ω i)⟫.
  -- Residual equality: for each `n` and `ω : ℕ → 𝓧`,
  -- `residual_abs n ω = residual_con n (restrictN n ω)`.
  have h_factor : ∀ n (ω : ℕ → 𝓧),
      ((∑ i ∈ Finset.range n,
          Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) (X i ω)
                    / M.density θ₀ (X i ω)))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ⟪h, ℓ (X i ω)⟫
        + (1/2 : ℝ) * fisherInformation M μ θ₀ ℓ h h)
      = logLikelihood M θ₀ h n (fun i : Fin n => ω i.val)
          - (⟪h, scoreSum ℓ n (fun i : Fin n => ω i.val)⟫
              - (1/2 : ℝ) * J_term) := by
    intro n ω
    simp only [logLikelihood, scoreSum, X, hJ_fisher, inner_smul_right, inner_sum]
    rw [Fin.sum_univ_eq_sum_range
          (fun i => Real.log
            (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) (ω i) / M.density θ₀ (ω i))),
        Fin.sum_univ_eq_sum_range (fun i => ⟪h, ℓ (ω i)⟫)]
    ring
  -- Set-level rewrite: {ω | ε ≤ |residual_abs n ω|} = (restrictN n)⁻¹' {ω' | ε ≤ |residual_con n
  -- ω'|}.
  have h_set_eq : ∀ n : ℕ,
      {ω : ℕ → 𝓧 | ε ≤ ‖((∑ i ∈ Finset.range n,
          Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) (X i ω)
                    / M.density θ₀ (X i ω)))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ⟪h, ℓ (X i ω)⟫
        + (1/2 : ℝ) * fisherInformation M μ θ₀ ℓ h h) - (0 : ℝ)‖}
        = (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) ⁻¹'
            {ω' : Fin n → 𝓧 | ε ≤ |logLikelihood M θ₀ h n ω'
                     - (⟪h, scoreSum ℓ n ω'⟫ - (1/2 : ℝ) * J_term)|} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_zero, Real.norm_eq_abs]
    rw [h_factor n ω]
  -- Rewrite `P {...}` as `(P.map restrictN n) {...}` via Measure.map_apply, then
  -- identify `P.map restrictN n` with `productMeasure M μ θ₀ n`.
  have h_measurable_set : ∀ n,
      MeasurableSet {ω' : Fin n → 𝓧 | ε ≤ |logLikelihood M θ₀ h n ω'
              - (⟪h, scoreSum ℓ n ω'⟫ - (1/2 : ℝ) * J_term)|} := by
    intro n
    refine measurableSet_le measurable_const ?_
    have hLL : Measurable (logLikelihood M θ₀ h n) :=
      logLikelihood_measurable M θ₀ h n
    have hΔ : Measurable (scoreSum ℓ n) := by
      unfold scoreSum
      exact (Finset.univ.measurable_sum
        (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
        ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
    exact ((hLL.sub ((Measurable.const_inner (c := h) hΔ).sub measurable_const))
      |>.abs)
  have h_meas_rw : ∀ n,
      P {ω : ℕ → 𝓧 | ε ≤ ‖((∑ i ∈ Finset.range n,
          Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) (X i ω)
                    / M.density θ₀ (X i ω)))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ⟪h, ℓ (X i ω)⟫
        + (1/2 : ℝ) * fisherInformation M μ θ₀ ℓ h h) - (0 : ℝ)‖}
      = productMeasure M μ θ₀ n
          {ω' : Fin n → 𝓧 | ε ≤ |logLikelihood M θ₀ h n ω'
                   - (⟪h, scoreSum ℓ n ω'⟫ - (1/2 : ℝ) * J_term)|} := by
    intro n
    rw [h_set_eq n]
    rw [← Measure.map_apply (h_restrict_meas n) (h_measurable_set n)]
    have h_map_eq : P.map (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
        = productMeasure M μ θ₀ n := by
      change Measure.map _ (Measure.infinitePi _) = _
      rw [show productMeasure M μ θ₀ n = Measure.pi (fun _ : Fin n => ν) from rfl]
      exact (AsymptoticStatistics.pi_const_eq_infinitePi_map ν n).symm
    rw [h_map_eq]
  -- Pull the rewrite through hLAN_ε and then convert ENNReal → ℝ.
  simp_rw [h_meas_rw] at hLAN_ε
  simp_rw [Measure.real_def]
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => by
    have : IsProbabilityMeasure (productMeasure M μ θ₀ n) := inferInstance
    exact measure_ne_top _ _)).mpr hLAN_ε

/-! ## Step 4 — Contiguity of local alternatives

From the log-normal limit of the likelihood ratio under `P^n_{θ₀}` (as given by Step 3's
second marginal — this is `N(-½ ⟨h, Jh⟩, ⟨h, Jh⟩)`), Le Cam's first lemma gives mutual
contiguity `P^n_{θ₀} ⊲⊳ P^n_{θ₀ + h/√n}`.

The three hypotheses `hL_meas`, `hL_is_log_ratio`, `h_log_weak` bridge from Step 3's output
(joint weak convergence) to the form `mutuallyContiguous_of_asymptotically_log_normal`
expects: marginal weak convergence of the log-likelihood ratio to `N(-v/2, v)`, plus the
identity `P_{θ₀+h/√n} = P_{θ₀}.withDensity (exp ∘ logLikelihood)`. -/

theorem contiguous_local_alternatives
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (_hℓ : Measurable ℓ)
    (_hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (_hJ_pd : Matrix.PosDef J)
    (_hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (h : Θ k)
    (hL_meas : ∀ n : ℕ, Measurable (logLikelihood M θ₀ h n))
    (hL_is_log_ratio : ∀ n : ℕ,
        productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n =
          (productMeasure M μ θ₀ n).withDensity
            (fun ω => ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))))
    (v : NNReal)
    (h_log_weak :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map (logLikelihood M θ₀ h n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    Contiguity.MutuallyContiguous (ι := ℕ)
      (Ω := fun n => Fin n → 𝓧) atTop
      (fun n => productMeasure M μ θ₀ n)
      (fun n => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) :=
  Contiguity.mutuallyContiguous_of_asymptotically_log_normal
    (Ω := fun n => Fin n → 𝓧)
    (fun n => productMeasure M μ θ₀ n)
    (fun n => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
    (fun n => logLikelihood M θ₀ h n) hL_meas hL_is_log_ratio v h_log_weak

/-! ## Step 5 — `L_h` as a Le Cam third-lemma tilted law

Combining contiguity (Step 4) with the joint weak convergence of `(T_n, log-lik)`
(Step 3) yields, via Le Cam's third lemma, that `T_n` under `P^n_{θ₀ + h/√n}` converges
weakly to the tilted law `L_h(B) = E[𝟙_B(S) · exp(⟨h, Δ⟩ − ½ ⟨h, J h⟩)]`. -/

/-- **Tilted marginal simplification**: converts Le Cam 3's natural output
`((π.map tilt_map).withDensity (exp∘snd)).map fst` to the LAN representation's form
`(π.withDensity (exp∘g)).map fst`, where `tilt_map p = (p.1, g p)`.

Two uses:
* Le Cam 3 gives weak convergence to `((π_tilted.withDensity (exp ∘ snd)).map fst)`.
* Step 5's conclusion uses `(π.withDensity (exp ∘ (affine tilt))).map fst`.

This lemma bridges the two forms via the general `Measure.withDensity_map_eq_map_withDensity`
plus `Measure.map_map`. -/
private lemma tilted_marginal_simplify
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (π : Measure (α × β)) (g : α × β → γ) (hg : Measurable g)
    (h : γ → ℝ) (hh : Measurable h) :
    ((π.map (fun p => (p.1, g p))).withDensity
        (fun q : α × γ => ENNReal.ofReal (h q.2))).map Prod.fst
      = (π.withDensity (fun p => ENNReal.ofReal (h (g p)))).map Prod.fst := by
  have h_tilt_meas : Measurable (fun p : α × β => (p.1, g p)) :=
    measurable_fst.prodMk hg
  have h_snd_ennreal_meas :
      Measurable (fun q : α × γ => ENNReal.ofReal (h q.2)) :=
    (hh.comp measurable_snd).ennreal_ofReal
  rw [Measure.withDensity_map_eq_map_withDensity π _ h_tilt_meas
    (fun q : α × γ => ENNReal.ofReal (h q.2)) h_snd_ennreal_meas]
  rw [MeasureTheory.Measure.map_map measurable_fst h_tilt_meas]
  rfl

/-! ## Product-level integral-comparison bound

These lemmas pass from the DQM-derived per-factor singular-mass control to
product-measure comparisons for `productMeasure` and `logLikelihood`.

This is the vdV §7.3 contiguity footing: it replaces the *exact* finite-`n` change-of-measure
identity `Q_n = P_n.withDensity(exp Lₙ)` (which forced absolute continuity hence common
support) by a DQM-derived *asymptotic* comparison. -/

/-! ### Per-factor decomposition

These lemmas all rest on the per-factor decomposition of the log-likelihood: writing
`r x := M.density (θ₀+(√n)⁻¹•h) x / M.density θ₀ x`, we have
`exp(logLikelihood … n ω) = ∏ᵢ exp(log (r (ω i)))`, and the per-factor "tilt density" w.r.t. `μ`
is `g₀ x := M.density θ₀ x · exp(log (r x))`, with mass
`c_n := ∫ g₀ dμ = 1 − deficit_n + excess_n`. -/

/-- Per-factor real density `g₀ x = p₀ x · exp(log(p'/p₀))`. On `{p₀>0,p'>0}` it equals `p'`, on
`{p₀>0,p'=0}` it equals `p₀` (the `exp∘log` junk), on `{p₀=0}` it equals `0`. -/
private noncomputable def expLogFactor
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) (x : 𝓧) : ℝ :=
  M.density θ₀ x * Real.exp (Real.log
    (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x / M.density θ₀ x))

private lemma expLogFactor_nonneg
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) (x : 𝓧) :
    0 ≤ expLogFactor M θ₀ h n x :=
  mul_nonneg (M.density_nonneg _ _) (Real.exp_pos _).le

private lemma expLogFactor_meas
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) :
    Measurable (expLogFactor M θ₀ h n) :=
  (M.density_meas _).mul
    (((M.density_meas _).div (M.density_meas _)).log.exp)

/-- Pointwise value of `expLogFactor` split by the support of `p₀` and `p'`. -/
private lemma expLogFactor_apply
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) (x : 𝓧) :
    expLogFactor M θ₀ h n x =
      if M.density θ₀ x = 0 then 0
      else if M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0 then M.density θ₀ x
      else M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x := by
  unfold expLogFactor
  set p₀ := M.density θ₀ x with hp₀
  set p' := M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x with hp'
  by_cases hp₀z : p₀ = 0
  · simp [hp₀z]
  · rw [if_neg hp₀z]
    by_cases hp'z : p' = 0
    · simp [hp'z, Real.log_zero, Real.exp_zero, mul_one]
    · rw [if_neg hp'z]
      have hp₀pos : 0 < p₀ := lt_of_le_of_ne (M.density_nonneg _ _) (Ne.symm hp₀z)
      have hp'pos : 0 < p' := lt_of_le_of_ne (M.density_nonneg _ _) (Ne.symm hp'z)
      rw [Real.exp_log (div_pos hp'pos hp₀pos)]
      field_simp

/-- `expLogFactor ≤ p₀ + p'` pointwise (each branch of `expLogFactor_apply` is `≤ p₀ + p'`). -/
private lemma expLogFactor_le
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) (x : 𝓧) :
    expLogFactor M θ₀ h n x
      ≤ M.density θ₀ x + M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x := by
  rw [expLogFactor_apply]
  by_cases hp₀z : M.density θ₀ x = 0
  · simp only [if_pos hp₀z]
    exact add_nonneg (M.density_nonneg _ _) (M.density_nonneg _ _)
  · rw [if_neg hp₀z]
    by_cases hp'z : M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0
    · simp only [if_pos hp'z]
      exact le_add_of_nonneg_right (M.density_nonneg _ _)
    · rw [if_neg hp'z]
      exact le_add_of_nonneg_left (M.density_nonneg _ _)

/-- `expLogFactor` is `μ`-integrable, dominated by the two integrable densities. -/
private lemma expLogFactor_integrable
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ h : Θ k) (n : ℕ)
    (hint : Integrable (M.density θ₀) μ)
    (hint' : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) μ) :
    Integrable (expLogFactor M θ₀ h n) μ := by
  refine Integrable.mono' (hint.add hint')
    (expLogFactor_meas M θ₀ h n).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (expLogFactor_nonneg M θ₀ h n x)]
  exact expLogFactor_le M θ₀ h n x

/-- **Per-factor mass identity.** The `μ`-mass of `expLogFactor` is `1 − deficit_n + excess_n`:
`∫ g₀ dμ = 1 − ∫_{p₀=0} p' dμ + ∫_{p'=0} p₀ dμ`. Proof: `∫ g₀ − ∫ p' = ∫ (g₀ − p')`, and `g₀ − p'`
is `−p'` on `{p₀=0}`, `p₀` on `{p₀>0,p'=0}`, `0` on `{p₀>0,p'>0}`. -/
private lemma expLogFactor_integral_eq
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ h : Θ k) (n : ℕ)
    (hint : Integrable (M.density θ₀) μ)
    (hint' : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) μ)
    (hnorm : ∫ x, M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ = 1) :
    ∫ x, expLogFactor M θ₀ h n x ∂μ
      = 1 - (∫ x in {x | M.density θ₀ x = 0},
              M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ)
          + ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
              M.density θ₀ x ∂μ := by
  set S₀ : Set 𝓧 := {x | M.density θ₀ x = 0} with hS₀def
  set S' : Set 𝓧 := {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0} with hS'def
  have hS₀_meas : MeasurableSet S₀ := (M.density_meas θ₀) (measurableSet_singleton 0)
  have hS'_meas : MeasurableSet S' :=
    (M.density_meas (θ₀ + (Real.sqrt n)⁻¹ • h)) (measurableSet_singleton 0)
  -- `∫ g₀ = ∫ p' + ∫ (g₀ − p')`, and the difference is supported on the singular sets.
  have hg₀int : Integrable (expLogFactor M θ₀ h n) μ :=
    expLogFactor_integrable M μ θ₀ h n hint hint'
  -- The pointwise difference `expLogFactor − p' = S'.indicator p₀ − S₀.indicator p'`.
  have hdiff : (fun x => expLogFactor M θ₀ h n x - M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)
      = fun x => S'.indicator (M.density θ₀) x
                 - S₀.indicator (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) x := by
    funext x
    rw [expLogFactor_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [hS₀def, hS'def, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hint_indic₀ : Integrable (S'.indicator (M.density θ₀)) μ := hint.indicator hS'_meas
  have hint_indic' : Integrable (S₀.indicator (M.density (θ₀ + (Real.sqrt n)⁻¹ • h))) μ :=
    hint'.indicator hS₀_meas
  have key : ∫ x, expLogFactor M θ₀ h n x ∂μ
        - ∫ x, M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ
      = (∫ x, S'.indicator (M.density θ₀) x ∂μ)
        - ∫ x, S₀.indicator (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) x ∂μ := by
    rw [← integral_sub hg₀int hint', hdiff, integral_sub hint_indic₀ hint_indic']
  rw [integral_indicator hS'_meas, integral_indicator hS₀_meas] at key
  rw [hnorm] at key
  linarith [key]

/-- **`exp(logLikelihood)` lintegral factorisation.** `∫⁻ ofReal(exp Lₙ) dP_n = (ofReal c_n)^n`,
where `c_n = ∫ expLogFactor dμ` is the per-factor mass. Proof: `ofReal(exp Lₙ ω) = ∏ᵢ eUnit(ωᵢ)`
with `eUnit x = ofReal(exp(log(p'/p₀)))`, then `lintegral_fin_nat_prod_eq_prod` factors the product
integral and `lintegral_withDensity_eq_lintegral_mul` reassembles the per-factor `μ`-integral. -/
private lemma expLogLikelihood_lintegral_eq
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (h : Θ k) (n : ℕ)
    (hint' : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) μ)
    (hint : Integrable (M.density θ₀) μ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω)) ∂(productMeasure M μ θ₀ n)
      = (ENNReal.ofReal (∫ x, expLogFactor M θ₀ h n x ∂μ)) ^ n := by
  -- per-factor ENNReal density `eUnit x = ofReal(exp(log(p'/p₀)))`.
  set eUnit : 𝓧 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (Real.log
      (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x / M.density θ₀ x))) with heUnit
  have heUnit_meas : Measurable eUnit :=
    (((M.density_meas _).div (M.density_meas _)).log.exp).ennreal_ofReal
  have hp₀_meas : Measurable (fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    (M.density_meas θ₀).ennreal_ofReal
  -- Rewrite the integrand as a product of per-coordinate `eUnit`s.
  have h_integrand : (fun ω : Fin n → 𝓧 =>
        ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω)))
      = fun ω => ∏ i, eUnit (ω i) := by
    funext ω
    unfold logLikelihood
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [h_integrand]
  -- Factor the product integral over the i.i.d. product measure.
  unfold productMeasure
  rw [lintegral_fin_nat_prod_eq_prod (fun _ => heUnit_meas)]
  -- Each factor: `∫⁻ eUnit dν₀ = ∫⁻ eUnit · ofReal p₀ dμ = ofReal(∫ expLogFactor dμ)`.
  have h_factor : ∀ _i : Fin n,
      ∫⁻ x, eUnit x ∂(μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
        = ENNReal.ofReal (∫ x, expLogFactor M θ₀ h n x ∂μ) := by
    intro _i
    rw [lintegral_withDensity_eq_lintegral_mul _ hp₀_meas heUnit_meas,
      ofReal_integral_eq_lintegral_ofReal
        (expLogFactor_integrable M μ θ₀ h n hint hint')
        (Filter.Eventually.of_forall (expLogFactor_nonneg M θ₀ h n))]
    refine lintegral_congr (fun x => ?_)
    rw [heUnit, Pi.mul_apply, ← ENNReal.ofReal_mul (M.density_nonneg θ₀ x), expLogFactor]
  rw [Finset.prod_congr rfl (fun i _ => h_factor i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The per-coordinate ENNReal density of the `exp∘log` tilt:
`eUnit x = ofReal(exp(log(p'/p₀)))`. -/
private noncomputable def expLogUnitE
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) (x : 𝓧) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (Real.log
    (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x / M.density θ₀ x)))

private lemma expLogUnitE_meas
    (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) :
    Measurable (expLogUnitE M θ₀ h n) :=
  (((M.density_meas _).div (M.density_meas _)).log.exp).ennreal_ofReal

/-- The per-factor tilt `ν̃ = ν₀.withDensity eUnit` equals `μ.withDensity (ofReal ∘ expLogFactor)`,
hence is a finite measure. -/
private lemma factorTilt_eq
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ h : Θ k) (n : ℕ) :
    (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).withDensity
        (expLogUnitE M θ₀ h n)
      = μ.withDensity (fun x => ENNReal.ofReal (expLogFactor M θ₀ h n x)) := by
  have hp_meas : Measurable (fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    (M.density_meas θ₀).ennreal_ofReal
  rw [← withDensity_mul _ hp_meas (expLogUnitE_meas M θ₀ h n)]
  refine withDensity_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Pi.mul_apply, expLogUnitE, expLogFactor]
  rw [← ENNReal.ofReal_mul (M.density_nonneg θ₀ x)]

/-- **`R_n` as an i.i.d. product.** `P_n.withDensity(ofReal(exp Lₙ)) = Measure.pi (fun _ => ν̃)`
where `ν̃ = ν₀.withDensity eUnit`. Same `pi_withDensity_prod` decomposition as
`logLikelihood_is_log_ratio`, minus the per-factor support hypothesis. -/
private lemma withDensity_expLogLikelihood_eq_pi
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ h : Θ k) (n : ℕ)
    (hint : Integrable (M.density θ₀) μ)
    (hint' : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) μ) :
    (productMeasure M μ θ₀ n).withDensity
        (fun ω => ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω)))
      = Measure.pi (fun _ : Fin n =>
          (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).withDensity
            (expLogUnitE M θ₀ h n)) := by
  have hp_meas : Measurable (fun x => ENNReal.ofReal (M.density θ₀ x)) :=
    (M.density_meas θ₀).ennreal_ofReal
  have hE_meas : Measurable (expLogUnitE M θ₀ h n) := expLogUnitE_meas M θ₀ h n
  -- Each per-factor tilt is a finite (hence sigma-finite) measure.
  haveI : IsFiniteMeasure
      ((μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).withDensity
        (expLogUnitE M θ₀ h n)) := by
    rw [factorTilt_eq]
    exact isFiniteMeasure_withDensity_ofReal
      (expLogFactor_integrable M μ θ₀ h n hint hint').hasFiniteIntegral
  -- `ofReal(exp Lₙ ω) = ∏ᵢ eUnit(ωᵢ)`; then `pi_withDensity_prod`.
  have h_integrand : (fun ω : Fin n → 𝓧 =>
        ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω)))
      = fun ω => ∏ i, expLogUnitE M θ₀ h n (ω i) := by
    funext ω
    unfold logLikelihood expLogUnitE
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [h_integrand]
  unfold productMeasure
  rw [pi_withDensity_prod (fun _ : Fin n => hE_meas)]

/-- The single-factor "good" set: both densities strictly positive. -/
private def goodSet (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) : Set 𝓧 :=
  {x | 0 < M.density θ₀ x ∧ 0 < M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x}

private lemma goodSet_meas (M : ParametricFamily 𝓧 (Θ k)) (θ₀ h : Θ k) (n : ℕ) :
    MeasurableSet (goodSet M θ₀ h n) :=
  (measurableSet_lt measurable_const (M.density_meas θ₀)).inter
    (measurableSet_lt measurable_const (M.density_meas (θ₀ + (Real.sqrt n)⁻¹ • h)))

/-- **Restriction agreement on the good rectangle.** `Q_n` and `R_n = P_n.withDensity(exp Lₙ)`
agree when restricted to `G_n = {ω | ∀ i, ω i ∈ good}`: on the good single-factor set both
per-factor `μ`-densities equal `p'`. -/
private lemma restrict_good_eq
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ h : Θ k) (n : ℕ)
    (hint : Integrable (M.density θ₀) μ)
    (hint' : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) μ) :
    (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).restrict
        (Set.univ.pi (fun _ : Fin n => goodSet M θ₀ h n))
      = ((productMeasure M μ θ₀ n).withDensity
          (fun ω => ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω)))).restrict
          (Set.univ.pi (fun _ : Fin n => goodSet M θ₀ h n)) := by
  have hgood_meas := goodSet_meas M θ₀ h n
  -- Per-factor: `ν'.restrict good = ν̃.restrict good`.
  have h_factor :
      (μ.withDensity fun x => ENNReal.ofReal
          (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)).restrict (goodSet M θ₀ h n)
        = ((μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).withDensity
            (expLogUnitE M θ₀ h n)).restrict (goodSet M θ₀ h n) := by
    rw [factorTilt_eq, restrict_withDensity hgood_meas, restrict_withDensity hgood_meas]
    refine withDensity_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hgood_meas]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    -- on `good`, `expLogFactor = p'`.
    rw [expLogFactor_apply]
    obtain ⟨hp₀, hp'⟩ := hx
    rw [if_neg (ne_of_gt hp₀), if_neg (ne_of_gt hp')]
  -- Lift to the product via `restrict_pi_pi`, using the `R_n` pi-form for the RHS.
  haveI : IsFiniteMeasure
      ((μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)).withDensity
        (expLogUnitE M θ₀ h n)) := by
    rw [factorTilt_eq]
    exact isFiniteMeasure_withDensity_ofReal
      (expLogFactor_integrable M μ θ₀ h n hint hint').hasFiniteIntegral
  rw [withDensity_expLogLikelihood_eq_pi M μ θ₀ h n hint hint']
  unfold productMeasure
  rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi]
  exact congrArg (fun ν => Measure.pi (fun _ : Fin n => ν)) h_factor

/-- Per-factor mass of the good-set complement: `ν'(goodᶜ) ≤ ofReal(deficit_n)`, where
`ν' = μ.withDensity(ofReal p')` and `deficit_n = ∫_{p₀=0} p' dμ`. On `goodᶜ`, `ν'` charges only
`{p₀=0}` (where `p'>0` forces `p₀=0`). -/
private lemma factor_goodCompl_le
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ h : Θ k) (n : ℕ)
    (hint' : Integrable (M.density (θ₀ + (Real.sqrt n)⁻¹ • h)) μ) :
    (μ.withDensity fun x => ENNReal.ofReal
        (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) (goodSet M θ₀ h n)ᶜ
      ≤ ENNReal.ofReal (∫ x in {x | M.density θ₀ x = 0},
          M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ) := by
  have hp'_meas : Measurable (fun x => ENNReal.ofReal
      (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) :=
    (M.density_meas _).ennreal_ofReal
  have hgood_meas := goodSet_meas M θ₀ h n
  have hS₀_meas : MeasurableSet {x | M.density θ₀ x = 0} :=
    (M.density_meas θ₀) (measurableSet_singleton 0)
  -- `ν'(goodᶜ) ≤ ν'({p₀=0})`, comparing indicator-weighted densities pointwise.
  have h_le : (μ.withDensity fun x => ENNReal.ofReal
        (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) (goodSet M θ₀ h n)ᶜ
      ≤ (μ.withDensity fun x => ENNReal.ofReal
        (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) {x | M.density θ₀ x = 0} := by
    rw [withDensity_apply _ hgood_meas.compl, withDensity_apply _ hS₀_meas,
      ← lintegral_indicator hgood_meas.compl, ← lintegral_indicator hS₀_meas]
    refine lintegral_mono (fun x => ?_)
    by_cases hx : x ∈ (goodSet M θ₀ h n)ᶜ
    · rw [Set.indicator_of_mem hx]
      by_cases hx₀ : M.density θ₀ x = 0
      · rw [Set.indicator_of_mem (show x ∈ {x | M.density θ₀ x = 0} from hx₀)]
      · -- `p₀ > 0` and `x ∉ good` force `p' = 0`.
        have hp₀ : 0 < M.density θ₀ x :=
          lt_of_le_of_ne (M.density_nonneg _ _) (Ne.symm hx₀)
        rw [Set.mem_compl_iff, goodSet, Set.mem_setOf_eq, not_and] at hx
        have hp' : M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0 :=
          le_antisymm (not_lt.mp (hx hp₀)) (M.density_nonneg _ _)
        rw [hp', ENNReal.ofReal_zero]; exact zero_le
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  refine le_trans h_le (le_of_eq ?_)
  rw [withDensity_apply _ hS₀_meas,
    ← ofReal_integral_eq_lintegral_ofReal
      (hint'.restrict)
      (ae_restrict_of_ae (Filter.Eventually.of_forall (M.density_nonneg _)))]

/-- The single-factor probability measure `ν_θ = μ.withDensity (ofReal p_θ)`. -/
private lemma factor_isProbabilityMeasure
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) (hPDF : IsPDFOf M μ) (θ : Θ k) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (M.density θ x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ)
      (Filter.Eventually.of_forall (M.density_nonneg θ)),
    hPDF.density_integral_eq_one θ, ENNReal.ofReal_one]

/-- **Product union bound.** `Q_n((univ.pi good)ᶜ) ≤ n · ν'(goodᶜ)` by i.i.d. sub-additivity over
coordinates (`measure_iUnion_fintype_le` + `measurePreserving_eval`). -/
private lemma productMeasure_goodCompl_le
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) (hPDF : IsPDFOf M μ)
    (θ₀ h : Θ k) (n : ℕ) :
    (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
        (Set.univ.pi (fun _ : Fin n => goodSet M θ₀ h n))ᶜ
      ≤ (n : ℝ≥0∞) * (μ.withDensity fun x => ENNReal.ofReal
          (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) (goodSet M θ₀ h n)ᶜ := by
  haveI : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal
      (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) :=
    factor_isProbabilityMeasure M μ hPDF _
  have hgood_meas := goodSet_meas M θ₀ h n
  -- `(univ.pi good)ᶜ ⊆ ⋃ i, eval i ⁻¹' goodᶜ`.
  have h_subset : (Set.univ.pi (fun _ : Fin n => goodSet M θ₀ h n))ᶜ
      ⊆ ⋃ i : Fin n, Function.eval i ⁻¹' (goodSet M θ₀ h n)ᶜ := by
    intro ω hω
    rw [Set.mem_compl_iff, Set.mem_univ_pi] at hω
    push Not at hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  calc (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
          (Set.univ.pi (fun _ : Fin n => goodSet M θ₀ h n))ᶜ
      ≤ (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
          (⋃ i : Fin n, Function.eval i ⁻¹' (goodSet M θ₀ h n)ᶜ) :=
        measure_mono h_subset
    _ ≤ ∑ i : Fin n, (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
          (Function.eval i ⁻¹' (goodSet M θ₀ h n)ᶜ) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _i : Fin n, (μ.withDensity fun x => ENNReal.ofReal
          (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) (goodSet M θ₀ h n)ᶜ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact (MeasureTheory.measurePreserving_eval
          (μ := fun _ : Fin n => μ.withDensity fun x => ENNReal.ofReal
            (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) i).measure_preimage
          hgood_meas.compl.nullMeasurableSet
    _ = (n : ℝ≥0∞) * (μ.withDensity fun x => ENNReal.ofReal
          (M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x)) (goodSet M θ₀ h n)ᶜ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Main comparison bound.** For the base/perturbed product measures and the log-likelihood
`Lₙ = logLikelihood M θ₀ h n`, there is a single rate `ρ → 0` such that for *every* bounded
continuous `f : 𝓨 d →ᵇ ℝ` and every `n`,
`|∫ f(T n ω) dQ_n − ∫ f(T n ω)·exp(Lₙ ω) dP_n| ≤ ‖f‖ · ρ_n`,
with `Q_n = productMeasure M μ (θ₀+(√n)⁻¹•h) n`, `P_n = productMeasure M μ θ₀ n`. One `ρ` works for
all `f` because `ρ` depends only on the (per-factor) singular masses, not on `f`.

This is exactly the `h_integral_comparison` hypothesis of
`Contiguity.weak_limit_under_Q_of_lecam_third_of_integral_comparison`, with `X := T n`,
`E := 𝓨 d`.

**Proof:** the two integrands differ only on the singular sets `{p_{θ₀}=0}` /
`{p_{θ₀+h/√n}=0}` lifted to the product (the `exp∘log` encoding deposits junk `1` there); bound by
explicit set-decomposition, `≤ ‖f‖ · n · (excess + deficit per-factor)` via product union-bound
sub-additivity, `→ 0` via `dqm_perturbation_excess_mass_tendsto` +
`dqm_perturbation_deficit_mass_tendsto` (derived internally from `hDQM` + `hPDF`). -/
theorem productMeasure_integral_comparison
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (_hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (hPDF : IsPDFOf M μ)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (h : Θ k) :
    ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) (n : ℕ),
        |∫ ω, f (T n ω) ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
          - ∫ ω, f (T n ω) * Real.exp (logLikelihood M θ₀ h n ω)
              ∂(productMeasure M μ θ₀ n)| ≤ ‖f‖ * ρ n := by
  classical
  -- Abbreviations. `Q n`, `R n`, the good rectangle `G n`, and the per-factor mass `c n`.
  set G : ∀ n, Set (Fin n → 𝓧) := fun n => Set.univ.pi (fun _ : Fin n => goodSet M θ₀ h n) with hG
  set c : ℕ → ℝ := fun n => ∫ x, expLogFactor M θ₀ h n x ∂μ with hc
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n =>
    integral_nonneg (fun x => expLogFactor_nonneg M θ₀ h n x)
  have hG_meas : ∀ n, MeasurableSet (G n) := fun n =>
    MeasurableSet.univ_pi (fun _ => goodSet_meas M θ₀ h n)
  -- Define `Q n`, `R n` as local names. `R n` is a finite measure with mass `(c n)^n`.
  set R : ∀ n, Measure (Fin n → 𝓧) := fun n => (productMeasure M μ θ₀ n).withDensity
      (fun ω => ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))) with hR
  have hR_meas_dens : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))) := fun n =>
    (Real.continuous_exp.measurable.comp (logLikelihood_measurable M θ₀ h n)).ennreal_ofReal
  have hR_univ : ∀ n, (R n) Set.univ = ENNReal.ofReal (c n) ^ n := by
    intro n
    rw [hR, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      expLogLikelihood_lintegral_eq M μ θ₀ h n
        (hPDF.density_integrable _) (hPDF.density_integrable _)]
  haveI hR_fin : ∀ n, IsFiniteMeasure (R n) := by
    intro n
    refine ⟨?_⟩
    rw [hR_univ n]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  -- `Q n` is a probability measure (instance hypothesis).
  -- Integrability of `f ∘ T` under both measures (bounded × finite).
  have hf_meas : ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) n,
      AEStronglyMeasurable (fun ω : Fin n → 𝓧 => f (T n ω))
        (productMeasure M μ θ₀ n) :=
    fun f n => (f.continuous.measurable.comp (hT_meas n)).aestronglyMeasurable
  have hf_int_Q : ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) n,
      Integrable (fun ω => f (T n ω)) (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) := by
    intro f n
    exact (integrable_const ‖f‖).mono'
      (f.continuous.measurable.comp (hT_meas n)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => f.norm_coe_le_norm _))
  have hf_int_R : ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) n,
      Integrable (fun ω => f (T n ω)) (R n) := by
    intro f n
    exact (integrable_const ‖f‖).mono'
      (f.continuous.measurable.comp (hT_meas n)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => f.norm_coe_le_norm _))
  -- Per-coordinate complement masses (probability `Q n`, finite `R n`), as reals.
  set qc : ℕ → ℝ := fun n =>
    ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ).toReal with hqc
  have hqc_nonneg : ∀ n, 0 ≤ qc n := fun n => ENNReal.toReal_nonneg
  -- `R n` and `Q n` agree on `G n`; in particular `R n (G n) = Q n (G n)`.
  have hRG_eq : ∀ n, (R n) (G n) =
      (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n) := by
    intro n
    have := restrict_good_eq M μ θ₀ h n (hPDF.density_integrable _) (hPDF.density_integrable _)
    have h1 : ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).restrict (G n)) Set.univ
        = ((R n).restrict (G n)) Set.univ := by rw [← this]
    rwa [Measure.restrict_apply_univ, Measure.restrict_apply_univ, eq_comm] at h1
  -- The change-of-measure: `∫ f(T n)·exp(Lₙ) dP_n = ∫ f(T n) dR_n`.
  have h_cm : ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) n,
      ∫ ω, f (T n ω) * Real.exp (logLikelihood M θ₀ h n ω) ∂(productMeasure M μ θ₀ n)
        = ∫ ω, f (T n ω) ∂(R n) := by
    intro f n
    have hstep :
        ∫ ω, f (T n ω) ∂(R n)
          = ∫ ω, (ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))).toReal • f (T n ω)
              ∂(productMeasure M μ θ₀ n) :=
      integral_withDensity_eq_integral_toReal_smul (hR_meas_dens n)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
    rw [hstep]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [smul_eq_mul,
      ENNReal.toReal_ofReal (Real.exp_pos (logLikelihood M θ₀ h n ω)).le]
    ring
  -- The complement-mass of `R n` equals `(c n)^n − Q n (G n)` (via the agreement on `G n`).
  have hRc_eq : ∀ n, ((R n) (G n)ᶜ).toReal = (c n) ^ n - 1 + qc n := by
    intro n
    have hsum : (R n) (G n) + (R n) (G n)ᶜ = (R n) Set.univ :=
      measure_add_measure_compl (hG_meas n)
    have hQsum : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)
        + (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ = 1 := by
      rw [measure_add_measure_compl (hG_meas n), measure_univ]
    -- Pass to reals. All masses are finite.
    have hRGc_lt : (R n) (G n)ᶜ ≠ ∞ := (measure_lt_top (R n) _).ne
    have hRG_lt : (R n) (G n) ≠ ∞ := (measure_lt_top (R n) _).ne
    have hQGc_lt : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ ≠ ∞ :=
      (measure_lt_top _ _).ne
    have hQG_lt : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n) ≠ ∞ :=
      (measure_lt_top _ _).ne
    have e1 : ((R n) (G n)).toReal + ((R n) (G n)ᶜ).toReal = (c n) ^ n := by
      rw [← ENNReal.toReal_add hRG_lt hRGc_lt, hsum, hR_univ n, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (hc_nonneg n)]
    have e2 : ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)).toReal + qc n = 1 := by
      rw [hqc, ← ENNReal.toReal_add hQG_lt hQGc_lt, hQsum, ENNReal.toReal_one]
    have e3 : ((R n) (G n)).toReal
        = ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)).toReal := by
      rw [hRG_eq n]
    -- combine: rc = m − RG = m − QG = m − (1 − qc) = m − 1 + qc.
    have : ((R n) (G n)ᶜ).toReal = (c n) ^ n - ((R n) (G n)).toReal := by linarith [e1]
    rw [this, e3]; linarith [e2]
  -- The per-(f, n) bound, with ρ_n = 2·qc n + |c n^n − 1|.
  have h_bound : ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) (n : ℕ),
      |∫ ω, f (T n ω) ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
        - ∫ ω, f (T n ω) * Real.exp (logLikelihood M θ₀ h n ω) ∂(productMeasure M μ θ₀ n)|
      ≤ ‖f‖ * (2 * qc n + |(c n) ^ n - 1|) := by
    intro f n
    rw [h_cm f n]
    -- Split both integrals over `G n` / `(G n)ᶜ`.
    rw [← integral_add_compl (hG_meas n) (hf_int_Q f n),
      ← integral_add_compl (hG_meas n) (hf_int_R f n)]
    -- The `G n` parts agree (restriction equality): `∫ x in s, g ∂μ = ∫ g ∂(μ.restrict s)`.
    have hGpart : ∫ ω in G n, f (T n ω)
          ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
        = ∫ ω in G n, f (T n ω) ∂(R n) :=
      congrArg (fun m => ∫ ω, f (T n ω) ∂m)
        (restrict_good_eq M μ θ₀ h n (hPDF.density_integrable _) (hPDF.density_integrable _))
    -- After cancellation only the complement integrals remain.
    have hcancel :
        (∫ ω in G n, f (T n ω) ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
          + (∫ ω in (G n)ᶜ, f (T n ω) ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
          - ((∫ ω in G n, f (T n ω) ∂(R n)) + ∫ ω in (G n)ᶜ, f (T n ω) ∂(R n))
        = (∫ ω in (G n)ᶜ, f (T n ω) ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
          - ∫ ω in (G n)ᶜ, f (T n ω) ∂(R n) := by
      rw [hGpart]; ring
    rw [hcancel]
    -- Triangle inequality + per-set bound `|∫_s f| ≤ ‖f‖ · μ(s).toReal`.
    refine le_trans (abs_sub _ _) ?_
    have hQbound : |∫ ω in (G n)ᶜ, f (T n ω)
          ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)| ≤ ‖f‖ * qc n := by
      rw [hqc, ← Real.norm_eq_abs]
      exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
        (fun x _ => f.norm_coe_le_norm _)
    have hRbound : |∫ ω in (G n)ᶜ, f (T n ω) ∂(R n)| ≤ ‖f‖ * ((R n) (G n)ᶜ).toReal := by
      rw [← Real.norm_eq_abs]
      exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
        (fun x _ => f.norm_coe_le_norm _)
    -- `‖f‖·qc + ‖f‖·rc ≤ ‖f‖·(2 qc + |c^n−1|)` using `rc = c^n − 1 + qc ≤ |c^n−1| + qc`.
    have hnorm_nonneg : 0 ≤ ‖f‖ := norm_nonneg f
    calc |∫ ω in (G n)ᶜ, f (T n ω) ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)|
            + |∫ ω in (G n)ᶜ, f (T n ω) ∂(R n)|
        ≤ ‖f‖ * qc n + ‖f‖ * ((R n) (G n)ᶜ).toReal := add_le_add hQbound hRbound
      _ ≤ ‖f‖ * (2 * qc n + |(c n) ^ n - 1|) := by
          rw [hRc_eq n]
          nlinarith [hnorm_nonneg, hqc_nonneg n, le_abs_self ((c n) ^ n - 1)]
  -- Assemble: ρ → 0 since `qc → 0` and `|c^n − 1| → 0`.
  refine ⟨fun n => 2 * qc n + |(c n) ^ n - 1|, ?_, h_bound⟩
  -- `qc n → 0`: squeeze `0 ≤ qc n ≤ n · deficit_n → 0`.
  have h_def := dqm_perturbation_deficit_mass_tendsto M μ θ₀ ℓ
    (hPDF.density_integrable θ₀) (fun t u => hPDF.density_integrable (θ₀ + t • u)) hDQM h
  have h_exc := dqm_perturbation_excess_mass_tendsto M μ θ₀ ℓ
    (hPDF.density_integrable θ₀) (fun t u => hPDF.density_integrable (θ₀ + t • u)) hDQM h
  have hqc_le : ∀ n, qc n ≤ (n : ℝ) *
      ∫ x in {x | M.density θ₀ x = 0}, M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ := by
    intro n
    have h1 := productMeasure_goodCompl_le M μ hPDF θ₀ h n
    have h2 := factor_goodCompl_le M μ θ₀ h n (hPDF.density_integrable _)
    have h3 : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ
        ≤ (n : ℝ≥0∞) * ENNReal.ofReal
          (∫ x in {x | M.density θ₀ x = 0}, M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ) :=
      le_trans h1 (by gcongr)
    calc qc n = ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ).toReal := rfl
      _ ≤ ((n : ℝ≥0∞) * ENNReal.ofReal
            (∫ x in {x | M.density θ₀ x = 0}, M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ)).toReal :=
          ENNReal.toReal_mono (by finiteness) h3
      _ = (n : ℝ) * ∫ x in {x | M.density θ₀ x = 0},
            M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal
            (integral_nonneg (fun x => M.density_nonneg _ _))]
  have hqc_tendsto : Filter.Tendsto qc Filter.atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_def
      (Filter.Eventually.of_forall hqc_nonneg) (Filter.Eventually.of_forall hqc_le)
  -- `|c^n − 1| → 0` since `c^n → 1` (proved via `Real.tendsto_one_add_pow_exp_of_tendsto`).
  have hcm1 : ∀ n, c n - 1 =
      (∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ)
        - ∫ x in {x | M.density θ₀ x = 0},
            M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ := by
    intro n
    change (∫ x, expLogFactor M θ₀ h n x ∂μ) - 1 = _
    rw [expLogFactor_integral_eq M μ θ₀ h n (hPDF.density_integrable _)
      (hPDF.density_integrable _) (hPDF.density_integral_eq_one _)]
    ring
  have h_ndiff : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (c n - 1)) Filter.atTop (𝓝 0) := by
    have hsub := h_exc.sub h_def
    simp only [sub_zero] at hsub
    refine hsub.congr (fun n => ?_)
    rw [hcm1 n]; ring
  have hcpow : Filter.Tendsto (fun n => (c n) ^ n) Filter.atTop (𝓝 1) := by
    have hpow := Real.tendsto_one_add_pow_exp_of_tendsto h_ndiff
    simp only [Real.exp_zero] at hpow
    refine hpow.congr (fun n => ?_)
    congr 1; ring
  have h_abs : Filter.Tendsto (fun n => |(c n) ^ n - 1|) Filter.atTop (𝓝 0) := by
    have hsub : Filter.Tendsto (fun n => (c n) ^ n - 1) Filter.atTop (𝓝 0) := by
      have := hcpow.sub (tendsto_const_nhds (x := (1 : ℝ)))
      simpa using this
    simpa using hsub.abs
  have hfin := (hqc_tendsto.const_mul (2 : ℝ)).add h_abs
  simpa using hfin

/-- **Bounded-measurable comparison bound.** Same singular-mass estimate as
`productMeasure_integral_comparison`, but for a uniformly bounded *measurable* integrand
`g n : (Fin n → 𝓧) → ℝ` (with `|g n ω| ≤ C`), rather than a bounded continuous `f ∘ T`.

For the base/perturbed product measures and `Lₙ = logLikelihood M θ₀ h n`, there is a single rate
`ρ → 0` (the *same* `ρ` as the BCF version: it depends only on the per-factor singular masses, not
on the integrand) such that for every `g` bounded by `C ≥ 0` and every `n`,
`|∫ g_n dQ_n − ∫ g_n·exp(Lₙ) dP_n| ≤ C · ρ_n`,
with `Q_n = productMeasure M μ (θ₀+(√n)⁻¹•h) n`, `P_n = productMeasure M μ θ₀ n`.

Needed by the **kernel-form** Le Cam transfer: after `integral_compProd`, the lifted comparison on
`(Fin n → 𝓧) × 𝓨 d` reduces to a base-space comparison of `g_n ω = ∫ f d(κ_n ω)`, which is bounded
measurable (`|g_n| ≤ ‖f‖`) but NOT of the form `f ∘ T` for a BCF `f`. This supplies the
`h_integral_comparison` hypothesis of
`Contiguity.weak_limit_under_Q_of_lecam_third_of_integral_comparison` with `E := 𝓨 d` and the
*Markov-kernel-integrated* test function in place of `f ∘ X`.

**Proof:** identical set-decomposition argument to `productMeasure_integral_comparison`; the only
change is `f (T n ω) ↝ g n ω` and `‖f‖ ↝ C`, using `|g n ω| ≤ C` where the BCF version used
`f.norm_coe_le_norm`. The complement-bound never used continuity of the integrand, only its
sup-bound, so it generalizes verbatim. -/
theorem productMeasure_integral_comparison_boundedMeasurable
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (_hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (hPDF : IsPDFOf M μ)
    (h : Θ k) :
    ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ (g : ∀ n, (Fin n → 𝓧) → ℝ) (C : ℝ),
        (∀ n, Measurable (g n)) → 0 ≤ C → (∀ n ω, |g n ω| ≤ C) → ∀ (n : ℕ),
        |∫ ω, g n ω ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
          - ∫ ω, g n ω * Real.exp (logLikelihood M θ₀ h n ω)
              ∂(productMeasure M μ θ₀ n)| ≤ C * ρ n := by
  classical
  -- Same abbreviations as the BCF version.
  set G : ∀ n, Set (Fin n → 𝓧) := fun n => Set.univ.pi (fun _ : Fin n => goodSet M θ₀ h n) with hG
  set c : ℕ → ℝ := fun n => ∫ x, expLogFactor M θ₀ h n x ∂μ with hc
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n =>
    integral_nonneg (fun x => expLogFactor_nonneg M θ₀ h n x)
  have hG_meas : ∀ n, MeasurableSet (G n) := fun n =>
    MeasurableSet.univ_pi (fun _ => goodSet_meas M θ₀ h n)
  set R : ∀ n, Measure (Fin n → 𝓧) := fun n => (productMeasure M μ θ₀ n).withDensity
      (fun ω => ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))) with hR
  have hR_meas_dens : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))) := fun n =>
    (Real.continuous_exp.measurable.comp (logLikelihood_measurable M θ₀ h n)).ennreal_ofReal
  have hR_univ : ∀ n, (R n) Set.univ = ENNReal.ofReal (c n) ^ n := by
    intro n
    rw [hR, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      expLogLikelihood_lintegral_eq M μ θ₀ h n
        (hPDF.density_integrable _) (hPDF.density_integrable _)]
  haveI hR_fin : ∀ n, IsFiniteMeasure (R n) := by
    intro n
    refine ⟨?_⟩
    rw [hR_univ n]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  -- Per-coordinate complement masses (probability `Q n`, finite `R n`), as reals.
  set qc : ℕ → ℝ := fun n =>
    ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ).toReal with hqc
  have hqc_nonneg : ∀ n, 0 ≤ qc n := fun n => ENNReal.toReal_nonneg
  -- `R n` and `Q n` agree on `G n`.
  have hRG_eq : ∀ n, (R n) (G n) =
      (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n) := by
    intro n
    have := restrict_good_eq M μ θ₀ h n (hPDF.density_integrable _) (hPDF.density_integrable _)
    have h1 : ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).restrict (G n)) Set.univ
        = ((R n).restrict (G n)) Set.univ := by rw [← this]
    rwa [Measure.restrict_apply_univ, Measure.restrict_apply_univ, eq_comm] at h1
  -- The complement-mass of `R n` equals `(c n)^n − 1 + qc n` (via the agreement on `G n`).
  have hRc_eq : ∀ n, ((R n) (G n)ᶜ).toReal = (c n) ^ n - 1 + qc n := by
    intro n
    have hsum : (R n) (G n) + (R n) (G n)ᶜ = (R n) Set.univ :=
      measure_add_measure_compl (hG_meas n)
    have hQsum : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)
        + (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ = 1 := by
      rw [measure_add_measure_compl (hG_meas n), measure_univ]
    have hRGc_lt : (R n) (G n)ᶜ ≠ ∞ := (measure_lt_top (R n) _).ne
    have hRG_lt : (R n) (G n) ≠ ∞ := (measure_lt_top (R n) _).ne
    have hQGc_lt : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ ≠ ∞ :=
      (measure_lt_top _ _).ne
    have hQG_lt : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n) ≠ ∞ :=
      (measure_lt_top _ _).ne
    have e1 : ((R n) (G n)).toReal + ((R n) (G n)ᶜ).toReal = (c n) ^ n := by
      rw [← ENNReal.toReal_add hRG_lt hRGc_lt, hsum, hR_univ n, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (hc_nonneg n)]
    have e2 : ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)).toReal + qc n = 1 := by
      rw [hqc, ← ENNReal.toReal_add hQG_lt hQGc_lt, hQsum, ENNReal.toReal_one]
    have e3 : ((R n) (G n)).toReal
        = ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)).toReal := by
      rw [hRG_eq n]
    have : ((R n) (G n)ᶜ).toReal = (c n) ^ n - ((R n) (G n)).toReal := by linarith [e1]
    rw [this, e3]; linarith [e2]
  -- The per-(g, C, n) bound, with ρ_n = 2·qc n + |c n^n − 1| (same ρ as the BCF version).
  refine ⟨fun n => 2 * qc n + |(c n) ^ n - 1|, ?_, ?_⟩
  · -- ρ → 0 (verbatim from the BCF version).
    have h_def := dqm_perturbation_deficit_mass_tendsto M μ θ₀ ℓ
      (hPDF.density_integrable θ₀) (fun t u => hPDF.density_integrable (θ₀ + t • u)) hDQM h
    have h_exc := dqm_perturbation_excess_mass_tendsto M μ θ₀ ℓ
      (hPDF.density_integrable θ₀) (fun t u => hPDF.density_integrable (θ₀ + t • u)) hDQM h
    have hqc_le : ∀ n, qc n ≤ (n : ℝ) *
        ∫ x in {x | M.density θ₀ x = 0}, M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ := by
      intro n
      have h1 := productMeasure_goodCompl_le M μ hPDF θ₀ h n
      have h2 := factor_goodCompl_le M μ θ₀ h n (hPDF.density_integrable _)
      have h3 : (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ
          ≤ (n : ℝ≥0∞) * ENNReal.ofReal
            (∫ x in {x | M.density θ₀ x = 0}, M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ) :=
        le_trans h1 (by gcongr)
      calc qc n = ((productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) (G n)ᶜ).toReal := rfl
        _ ≤ ((n : ℝ≥0∞) * ENNReal.ofReal
              (∫ x in {x | M.density θ₀ x = 0},
                M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ)).toReal :=
            ENNReal.toReal_mono (by finiteness) h3
        _ = (n : ℝ) * ∫ x in {x | M.density θ₀ x = 0},
              M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal
              (integral_nonneg (fun x => M.density_nonneg _ _))]
    have hqc_tendsto : Filter.Tendsto qc Filter.atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_def
        (Filter.Eventually.of_forall hqc_nonneg) (Filter.Eventually.of_forall hqc_le)
    have hcm1 : ∀ n, c n - 1 =
        (∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ)
          - ∫ x in {x | M.density θ₀ x = 0},
              M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ := by
      intro n
      change (∫ x, expLogFactor M θ₀ h n x ∂μ) - 1 = _
      rw [expLogFactor_integral_eq M μ θ₀ h n (hPDF.density_integrable _)
        (hPDF.density_integrable _) (hPDF.density_integral_eq_one _)]
      ring
    have h_ndiff : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (c n - 1)) Filter.atTop (𝓝 0) := by
      have hsub := h_exc.sub h_def
      simp only [sub_zero] at hsub
      refine hsub.congr (fun n => ?_)
      rw [hcm1 n]; ring
    have hcpow : Filter.Tendsto (fun n => (c n) ^ n) Filter.atTop (𝓝 1) := by
      have hpow := Real.tendsto_one_add_pow_exp_of_tendsto h_ndiff
      simp only [Real.exp_zero] at hpow
      refine hpow.congr (fun n => ?_)
      congr 1; ring
    have h_abs : Filter.Tendsto (fun n => |(c n) ^ n - 1|) Filter.atTop (𝓝 0) := by
      have hsub : Filter.Tendsto (fun n => (c n) ^ n - 1) Filter.atTop (𝓝 0) := by
        have := hcpow.sub (tendsto_const_nhds (x := (1 : ℝ)))
        simpa using this
      simpa using hsub.abs
    have hfin := (hqc_tendsto.const_mul (2 : ℝ)).add h_abs
    simpa using hfin
  · -- The per-(g, C, n) bound itself.
    intro g C hg_meas hC hg_bound n
    -- `R n` is finite; `g n` is bounded by `C`, hence integrable under `Q n` and `R n`.
    have hf_int_Q : Integrable (fun ω => g n ω)
        (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) :=
      (integrable_const C).mono' (hg_meas n).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => by
          simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hg_bound n ω))
    have hf_int_R : Integrable (fun ω => g n ω) (R n) :=
      (integrable_const C).mono' (hg_meas n).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => by
          simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hg_bound n ω))
    -- The change-of-measure: `∫ g_n·exp(Lₙ) dP_n = ∫ g_n dR_n`.
    have h_cm :
        ∫ ω, g n ω * Real.exp (logLikelihood M θ₀ h n ω) ∂(productMeasure M μ θ₀ n)
          = ∫ ω, g n ω ∂(R n) := by
      have hstep :
          ∫ ω, g n ω ∂(R n)
            = ∫ ω, (ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))).toReal • g n ω
                ∂(productMeasure M μ θ₀ n) :=
        integral_withDensity_eq_integral_toReal_smul (hR_meas_dens n)
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
      rw [hstep]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [smul_eq_mul,
        ENNReal.toReal_ofReal (Real.exp_pos (logLikelihood M θ₀ h n ω)).le]
      ring
    rw [h_cm]
    -- Split both integrals over `G n` / `(G n)ᶜ`.
    rw [← integral_add_compl (hG_meas n) hf_int_Q,
      ← integral_add_compl (hG_meas n) hf_int_R]
    -- The `G n` parts agree (restriction equality).
    have hGpart : ∫ ω in G n, g n ω
          ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
        = ∫ ω in G n, g n ω ∂(R n) :=
      congrArg (fun m => ∫ ω, g n ω ∂m)
        (restrict_good_eq M μ θ₀ h n (hPDF.density_integrable _) (hPDF.density_integrable _))
    have hcancel :
        (∫ ω in G n, g n ω ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
          + (∫ ω in (G n)ᶜ, g n ω ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
          - ((∫ ω in G n, g n ω ∂(R n)) + ∫ ω in (G n)ᶜ, g n ω ∂(R n))
        = (∫ ω in (G n)ᶜ, g n ω ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
          - ∫ ω in (G n)ᶜ, g n ω ∂(R n) := by
      rw [hGpart]; ring
    rw [hcancel]
    refine le_trans (abs_sub _ _) ?_
    have hQbound : |∫ ω in (G n)ᶜ, g n ω
          ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)| ≤ C * qc n := by
      rw [hqc, ← Real.norm_eq_abs]
      exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
        (fun x _ => by rw [Real.norm_eq_abs]; exact hg_bound n x)
    have hRbound : |∫ ω in (G n)ᶜ, g n ω ∂(R n)| ≤ C * ((R n) (G n)ᶜ).toReal := by
      rw [← Real.norm_eq_abs]
      exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
        (fun x _ => by rw [Real.norm_eq_abs]; exact hg_bound n x)
    calc |∫ ω in (G n)ᶜ, g n ω ∂(productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)|
            + |∫ ω in (G n)ᶜ, g n ω ∂(R n)|
        ≤ C * qc n + C * ((R n) (G n)ᶜ).toReal := add_le_add hQbound hRbound
      _ ≤ C * (2 * qc n + |(c n) ^ n - 1|) := by
          rw [hRc_eq n]
          nlinarith [hC, hqc_nonneg n, le_abs_self ((c n) ^ n - 1)]

/-- **Companion scalar.** The base-measure mass of `exp(logLikelihood)` tends to `1`:
`∫ exp(Lₙ ω) dP_n → 1`, with `P_n = productMeasure M μ θ₀ n`.

This is exactly the `h_mass` hypothesis of
`Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one`.

**Proof:** `∫ exp(Lₙ) dP_n = Q_n(univ) − (deficit mass) = 1 − n·(deficit per-factor) → 1`
by `dqm_perturbation_deficit_mass_tendsto` (the perturbed product measure is a probability
measure, and `exp(Lₙ)` integrates the perturbed density off the base-singular set), derived
internally from `hDQM` + `hPDF`. -/
theorem productMeasure_integral_exp_logLikelihood_tendsto_one
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (_hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (hPDF : IsPDFOf M μ)
    (h : Θ k) :
    Filter.Tendsto
      (fun n => ∫ ω, Real.exp (logLikelihood M θ₀ h n ω) ∂(productMeasure M μ θ₀ n))
      Filter.atTop (𝓝 1) := by
  -- Per-factor mass `c n = ∫ expLogFactor dμ`; the product integral equals `(c n)^n`.
  set c : ℕ → ℝ := fun n => ∫ x, expLogFactor M θ₀ h n x ∂μ with hc
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n =>
    integral_nonneg (fun x => expLogFactor_nonneg M θ₀ h n x)
  have h_eq : ∀ n, ∫ ω, Real.exp (logLikelihood M θ₀ h n ω) ∂(productMeasure M μ θ₀ n)
      = (c n) ^ n := by
    intro n
    have hexp_meas : Measurable (fun ω => Real.exp (logLikelihood M θ₀ h n ω)) :=
      Real.continuous_exp.measurable.comp (logLikelihood_measurable M θ₀ h n)
    rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
        hexp_meas.aestronglyMeasurable,
      expLogLikelihood_lintegral_eq M μ θ₀ h n
        (hPDF.density_integrable _) (hPDF.density_integrable _),
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (hc_nonneg n)]
  -- `c n − 1 = excess_n − deficit_n`, so `n·(c n − 1) → 0` by the two singular-mass lemmas.
  have hcm1 : ∀ n, c n - 1 =
      (∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ)
        - ∫ x in {x | M.density θ₀ x = 0},
            M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ := by
    intro n
    change (∫ x, expLogFactor M θ₀ h n x ∂μ) - 1 = _
    rw [expLogFactor_integral_eq M μ θ₀ h n (hPDF.density_integrable _)
      (hPDF.density_integrable _) (hPDF.density_integral_eq_one _)]
    ring
  have h_def := dqm_perturbation_deficit_mass_tendsto M μ θ₀ ℓ
    (hPDF.density_integrable θ₀) (fun t u => hPDF.density_integrable (θ₀ + t • u)) hDQM h
  have h_exc := dqm_perturbation_excess_mass_tendsto M μ θ₀ ℓ
    (hPDF.density_integrable θ₀) (fun t u => hPDF.density_integrable (θ₀ + t • u)) hDQM h
  have h_ndiff : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (c n - 1)) Filter.atTop (𝓝 0) := by
    have hsub := h_exc.sub h_def
    simp only [sub_zero] at hsub
    refine hsub.congr (fun n => ?_)
    rw [hcm1 n]; ring
  -- `(c n)^n = (1 + (c n − 1))^n → exp 0 = 1`.
  have hpow := Real.tendsto_one_add_pow_exp_of_tendsto h_ndiff
  simp only [Real.exp_zero] at hpow
  refine hpow.congr (fun n => ?_)
  rw [h_eq n]; congr 1; ring

/-- **Integrability companion.** `exp(logLikelihood M θ₀ h n)` is integrable under the base
product measure `P_n = productMeasure M μ θ₀ n` for every `n`.

This is the `h_exp_int` hypothesis of
`Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one`. It is a finite-`n` fact
(NOT asymptotic): the perturbed product measure restricted off the base-singular set has a Radon–
Nikodym density `exp(Lₙ)` w.r.t. `P_n`, and that piece has mass `≤ 1` since the perturbed measure
is a probability measure.

**Proof:** `exp(Lₙ ω) = ∏ᵢ p_{θ₀+h/√n}(ωᵢ)/p_{θ₀}(ωᵢ)` on `{∀i, p_{θ₀}(ωᵢ) > 0}`;
its `P_n`-integral over that set is `≤ Q_n(univ) = 1`. -/
theorem productMeasure_exp_logLikelihood_integrable
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (_hℓ : Measurable ℓ)
    (_hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (hPDF : IsPDFOf M μ)
    (h : Θ k) :
    ∀ n : ℕ, Integrable (fun ω => Real.exp (logLikelihood M θ₀ h n ω))
      (productMeasure M μ θ₀ n) := by
  intro n
  have hexp_meas : Measurable (fun ω => Real.exp (logLikelihood M θ₀ h n ω)) :=
    Real.continuous_exp.measurable.comp (logLikelihood_measurable M θ₀ h n)
  refine ⟨hexp_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
  rw [expLogLikelihood_lintegral_eq M μ θ₀ h n
      (hPDF.density_integrable _) (hPDF.density_integrable _)]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

theorem limit_law_under_h
    [HasOuterApproxClosed (𝓨 d)] [BorelSpace (𝓨 d)]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- Model regularity: needed to derive the integral comparison internally from `hDQM`.
    (hPDF : IsPDFOf M μ)
    (J : Matrix (Fin k) (Fin k) ℝ) (_hJ_pd : Matrix.PosDef J)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (_h : Θ k)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (L_h : Measure (𝓨 d)) [IsProbabilityMeasure L_h]
    (h_weak_under_h :
      WeakConverges
        (fun n => (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • _h) n).map (T n)) L_h)
    -- The subsequence `φ` from Step 2 along which `(T, Δ)` converges weakly to `π`.
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h_subseq_joint_log :
      WeakConverges
        (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, logLikelihood M θ₀ _h (φ k_idx) ω)))
        (π.map (fun p =>
          (p.1, ⟪_h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫))))
    -- Log-likelihood: measurable. (The asymptotic integral comparison is derived internally
    -- from `hDQM` via the contiguity footing, so no exact change-of-measure identity is needed.)
    (hL_meas : ∀ n : ℕ, Measurable (logLikelihood M θ₀ _h n))
    -- Asymptotic log-normality of `log dQ/dP` (Step 3 output) — used to derive UI.
    (vLog : NNReal)
    (hLogLik_weak :
        WeakConverges
          (fun n => (productMeasure M μ θ₀ n).map (logLikelihood M θ₀ _h n))
          (ProbabilityTheory.gaussianReal (-(vLog : ℝ) / 2) vLog))
    -- Gaussian MGF at `_h` via the tilted joint law.  These package the multivariate
    -- Gaussian-MGF identities that Mathlib currently lacks (`π.map snd ~ N(0, J)` + MGF).
    (h_exp_int_πtilt :
        Integrable (fun q : 𝓨 d × ℝ => Real.exp q.2)
          (π.map (fun p : 𝓨 d × Θ k =>
            (p.1, ⟪_h, p.2⟫ - (1 / 2 : ℝ) *
              ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫))))
    (h_exp_int_πtilt_eq_one :
        ∫ q, Real.exp q.2 ∂
          (π.map (fun p : 𝓨 d × Θ k =>
            (p.1, ⟪_h, p.2⟫ - (1 / 2 : ℝ) *
              ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫)))
          = 1) :
    L_h = Measure.map Prod.fst
      (π.withDensity (fun p => ENNReal.ofReal
        (Real.exp (⟪_h, p.2⟫ - (1 / 2 : ℝ) *
          ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫)))) := by
  -- Abbreviate the affine tilt as a single function for readability (via `let`, so
  -- `g` / `tilt_map` unfold transparently into their lambda bodies).
  let g : Θ k → ℝ := fun δ =>
    ⟪_h, δ⟫ - (1 / 2 : ℝ) *
      ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫
  let tilt_map : 𝓨 d × Θ k → 𝓨 d × ℝ := fun p => (p.1, g p.2)
  -- Measurability of `g` and `tilt_map` (used to build the Le Cam 3 joint).
  have hg_meas : Measurable g :=
    (continuous_const.inner continuous_id).measurable.sub measurable_const
  have htilt_meas : Measurable tilt_map :=
    measurable_fst.prodMk (hg_meas.comp measurable_snd)
  haveI h_tilt_prob : IsProbabilityMeasure (π.map tilt_map) :=
    MeasureTheory.Measure.isProbabilityMeasure_map htilt_meas.aemeasurable
  -- Comparison companions, derived internally from `hDQM` + `hPDF` (the exact change-of-measure
  -- identity is replaced by DQM-derived asymptotic singular-mass control).
  have h_exp_int_full :=
    productMeasure_exp_logLikelihood_integrable M μ θ₀ ℓ hℓ hDQM hPDF _h
  have h_mass_full :=
    productMeasure_integral_exp_logLikelihood_tendsto_one M μ θ₀ ℓ hℓ hDQM hPDF _h
  -- Full-sequence UI of `exp(logLikelihood)` via the contiguity-footing variant.
  have h_UI_full := Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one
    (Ω := fun n => Fin n → 𝓧)
    (fun n => productMeasure M μ θ₀ n)
    (fun n => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • _h) n)
    (fun n => logLikelihood M θ₀ _h n) hL_meas h_exp_int_full h_mass_full vLog hLogLik_weak
  -- Specialise UI to the subsequence `φ` (use `StrictMono.id_le`, i.e. `n ≤ φ n`).
  have h_UI_subseq : ∀ ε : ℝ, 0 < ε →
      ∃ Mbd : ℝ, 0 ≤ Mbd ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (logLikelihood M θ₀ _h (φ n) ω) -
            min (Real.exp (logLikelihood M θ₀ _h (φ n) ω)) Mbd
          ∂(productMeasure M μ θ₀ (φ n)) ≤ ε := by
    intro ε hε
    obtain ⟨Mbd, hMbd, N₀, hN₀⟩ := h_UI_full ε hε
    refine ⟨Mbd, hMbd, N₀, fun n hn => hN₀ (φ n) (le_trans hn (hφ.id_le n))⟩
  -- Main integral-comparison bound (full sequence), then specialise to `φ`.
  obtain ⟨ρ, hρ_tendsto, hρ_bound⟩ :=
    productMeasure_integral_comparison M μ θ₀ ℓ hℓ hDQM hPDF T hT_meas _h
  have h_int_cmp_subseq :
      ∃ ρ' : ℕ → ℝ, Filter.Tendsto ρ' Filter.atTop (𝓝 0) ∧
        ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) (n : ℕ),
          |∫ ω, f (T (φ n) ω)
              ∂(productMeasure M μ (θ₀ + (Real.sqrt (φ n))⁻¹ • _h) (φ n))
            - ∫ ω, f (T (φ n) ω) * Real.exp (logLikelihood M θ₀ _h (φ n) ω)
                ∂(productMeasure M μ θ₀ (φ n))| ≤ ‖f‖ * ρ' n :=
    ⟨ρ ∘ φ, hρ_tendsto.comp hφ.tendsto_atTop, fun f n => hρ_bound f (φ n)⟩
  -- Apply Le Cam's third lemma (contiguity-footing variant) along the subsequence `φ`,
  -- with target `π.map tilt_map`.
  have h_lecam := Contiguity.weak_limit_under_Q_of_lecam_third_of_integral_comparison
    (Ω := fun n => Fin (φ n) → 𝓧) (E := 𝓨 d)
    (fun n => productMeasure M μ θ₀ (φ n))
    (fun n => productMeasure M μ (θ₀ + (Real.sqrt (φ n))⁻¹ • _h) (φ n))
    (fun n => T (φ n)) (fun n => logLikelihood M θ₀ _h (φ n))
    (fun n => hT_meas (φ n)) (fun n => hL_meas (φ n))
    h_int_cmp_subseq
    (π.map tilt_map) h_subseq_joint_log
    h_UI_subseq h_exp_int_πtilt h_exp_int_πtilt_eq_one
  -- Subsequence version of `h_weak_under_h`: `(Q_{φ n}).map T_{φ n} ⇝ L_h`.
  have h_weak_subseq :
      WeakConverges
        (fun n => (productMeasure M μ (θ₀ + (Real.sqrt (φ n))⁻¹ • _h) (φ n)).map (T (φ n)))
        L_h :=
    fun f => (h_weak_under_h f).comp hφ.tendsto_atTop
  -- Weak limits are unique on `𝓨 d` (Polish / BorelSpace + HasOuterApproxClosed).
  have h_target_prob :
      IsProbabilityMeasure
        (((π.map tilt_map).withDensity
          (fun q : 𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst) := by
    have h_mass_one :
        ((π.map tilt_map).withDensity
          (fun q : 𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))) Set.univ = 1 := by
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
          MeasureTheory.setLIntegral_univ]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_exp_int_πtilt
        (Filter.Eventually.of_forall (fun q => (Real.exp_pos _).le))]
      rw [h_exp_int_πtilt_eq_one, ENNReal.ofReal_one]
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.map_apply measurable_fst MeasurableSet.univ,
        Set.preimage_univ]
    exact h_mass_one
  have h_L_h_eq :
      L_h = ((π.map tilt_map).withDensity
        (fun q : 𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst := by
    refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure ?_
    intro f
    exact tendsto_nhds_unique (h_weak_subseq f) (h_lecam f)
  -- Re-express the RHS via `tilted_marginal_simplify` to match the target form.
  rw [h_L_h_eq]
  exact tilted_marginal_simplify π (fun p : 𝓨 d × Θ k => g p.2)
    (hg_meas.comp measurable_snd) Real.exp Real.continuous_exp.measurable

/-! ## Step 6 — Conditional-distribution kernel

`π` has second marginal `N(0, J)`; its condensed form gives a Markov kernel via
`Kernel.condDistrib`, consuming `δ ∼ N(0, J)`. To feed Gaussian-shift draws
`x ∼ N(h, J⁻¹)` into this kernel we **pre-compose with the linear action of `J`**:
multiplying by `J` maps `N(h, J⁻¹)` to `N(J h, J)`, matching the marginal scale
that `condDistrib fst snd π` expects. This composed kernel is the one claimed by
the main theorem.

Matches vdV §7.10's `κ' := κ ∘ J`. Without the pre-composition, `(gauss h).bind κ`
is type-correct but semantically wrong (it would pair J⁻¹-covariance arguments
with a J-covariance kernel). -/

/-- The representation kernel: `condDistrib fst snd π` pre-composed with the linear
action of `J`. Defined via `GaussianShift.matrixAction` (which lives with the other
Gaussian-shift helpers). See the docstring above for motivation. -/
noncomputable def representationKernel
    (J : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π] :
    Kernel (Θ k) (𝓨 d) :=
  (condDistrib (fun p : 𝓨 d × Θ k => p.1) (fun p => p.2) π).comap
    (GaussianShift.matrixAction J) (GaussianShift.matrixAction_measurable J)

instance representationKernel_isMarkov
    (J : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π] :
    IsMarkovKernel (representationKernel J π) := by
  unfold representationKernel
  infer_instance

/-! ## Step 7 — `N(h, J⁻¹) >>= κ ∘ J = L_h`

The Gaussian-specific content is expressed by the hypothesis
`hTilt : GaussianShift.HasTiltedLinearPushforward gauss (π.map snd) J`, which bundles
"J-pushforward of `N(h, J⁻¹)` equals `N(0, J)` tilted by `exp(⟨h, y⟩ − ½ ⟨h, J h⟩)`".
The remaining measure-theoretic algebra is carried by two purely general bridges:

* `Measure.bind_map_eq_bind_comap` — `(μ.map f).bind κ = μ.bind (κ.comap f)`;
* `Measure.withDensity_bind_condDistrib` — `(ν.withDensity f).bind (condDistrib fst snd π)
  = (π.withDensity (f ∘ snd)).map fst` when `ν = π.map snd`.

The proof chains these three identities with the preceding tilted-law formula
`_hL_h_formula`. -/

theorem gaussianShift_bind_eq_limit
    [StandardBorelSpace (𝓨 d)] [Nonempty (𝓨 d)]
    (J : Matrix (Fin k) (Fin k) ℝ) (_hJ_pd : Matrix.PosDef J)
    (gauss : Θ k → Measure (Θ k))
    (_hGauss : GaussianShift.IsGaussianShift gauss J⁻¹)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (_h : Θ k) (L_h : Measure (𝓨 d)) [IsProbabilityMeasure L_h]
    (hTilt : GaussianShift.HasTiltedLinearPushforward gauss (π.map Prod.snd) J)
    (_hL_h_formula : L_h = Measure.map Prod.fst
      (π.withDensity (fun p => ENNReal.ofReal
        (Real.exp (⟪_h, p.2⟫ - (1 / 2 : ℝ) *
          ⟪_h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) _h))⟫))))) :
    L_h = (gauss _h).bind (representationKernel J π) := by
  -- Measurability of the density appearing on the RHS of `hTilt _h`, needed by the
  -- general `withDensity_bind_condDistrib` bridge.
  have h_density_meas :
      Measurable (fun y : Θ k =>
        ENNReal.ofReal (Real.exp (⟪_h, y⟫ -
          (1 / 2 : ℝ) * ⟪_h, GaussianShift.matrixAction J _h⟫))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Real.continuous_exp.measurable.comp ?_
    refine Measurable.sub ?_ measurable_const
    exact (continuous_const.inner continuous_id).measurable
  -- Rewrite L_h via the Step-5 formula.
  rw [_hL_h_formula]
  -- Unfold `representationKernel` to expose the `comap (matrixAction J)` structure.
  unfold representationKernel
  -- Flip `bind (κ.comap f) → (μ.map f).bind κ` via `bind_map_eq_bind_comap`.
  rw [← Measure.bind_map_eq_bind_comap (gauss _h) (GaussianShift.matrixAction J)
      (GaussianShift.matrixAction_measurable J) _]
  -- Apply the Gaussian tilt identity: `(gauss _h).map (matrixAction J)` equals
  -- `(π.map snd).withDensity (exp tilt)`.
  rw [hTilt _h]
  -- Apply the measure-theoretic bridge: pushing the density through `condDistrib`.
  rw [Measure.withDensity_bind_condDistrib π _ h_density_meas]
  -- Both `withDensity` integrands are defeq:
  -- `matrixAction J _h = WithLp.equiv.symm ∘ J.mulVec ∘ WithLp.equiv`.
  rfl

/-! ## Step 8 — Subsequence limits ⇒ full-sequence limit

Every subsequence of `(T_n, Δ_n)` has (by Prohorov) a sub-subsequence with weak limit
`(S', Δ')`; by Steps 3–7 the induced `L_h` depends only on the joint law's Radon-Nikodym
derivative expression, which is uniquely determined by `Δ ∼ N(0, J)`. Hence every
sub-subsequence has the same limit, and Urysohn's principle (`tendsto_of_subseq_tendsto`)
gives full-sequence weak convergence. -/

theorem representation_full_sequence
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (_ℓ : 𝓧 → Θ k)
    (_J : Matrix (Fin k) (Fin k) ℝ) (_hJ_pd : Matrix.PosDef _J)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (_hT_meas : ∀ n, Measurable (T n))
    (L : Θ k → Measure (𝓨 d)) [∀ h, IsProbabilityMeasure (L h)]
    -- Every subsequence of the laws admits a further subsequence converging weakly to `L h`.
    (h_subseq_convergence : ∀ _h : Θ k, ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        WeakConverges
          (fun j => (productMeasure M μ (θ₀ + (Real.sqrt (φ (ψ j)))⁻¹ • _h) (φ (ψ j))).map
            (T (φ (ψ j)))) (L _h)) :
    ∀ _h : Θ k,
      WeakConverges
        (fun n => (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • _h) n).map (T n)) (L _h) := by
  intro h f
  -- Apply the Urysohn subsequence principle on the test-function-integral sequence.
  apply SubsequenceLimit.tendsto_of_subseq_tendsto
  intro φ hφ_mono
  obtain ⟨ψ, hψ_mono, hψ_weak⟩ := h_subseq_convergence h φ hφ_mono
  exact ⟨ψ, hψ_mono, hψ_weak f⟩

/-! ## Auxiliary theorem: `LAN_representation_of_gaussianShift`

Assembly of Steps 1–8. Given DQM at `θ₀`, non-singular Fisher information `J`, and
weak convergence `T_n ⇝ L_h` under each `P^n_{θ₀ + h/√n}`, there exists a Markov
kernel `κ` such that `L_h = gauss h >>= κ` for every `h`, provided `gauss` is a
Gaussian shift with covariance `J⁻¹`. -/

theorem LAN_representation_of_gaussianShift
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : Θ k → Measure (𝓨 d)) [∀ h, IsProbabilityMeasure (L h)]
    (hT_weak : ∀ h : Θ k,
      WeakConverges
        (fun n => (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map (T n)) (L h))
    (gauss : Θ k → Measure (Θ k))
    (hGauss : GaussianShift.IsGaussianShift gauss J⁻¹)
    [StandardBorelSpace (𝓨 d)] [Nonempty (𝓨 d)]
    [HasOuterApproxClosed (𝓨 d)] [BorelSpace (𝓨 d)]
    -- Model-level regularity: normalisation + integrability for every parameter.
    (hPDF : IsPDFOf M μ) :
    -- The LAN/Le Cam transfer routes through a DQM-derived asymptotic integral comparison
    -- rather than an exact change-of-measure identity, so no common-support assumption is needed.
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k, L h = (gauss h).bind κ := by
  -- Derive `IsProbabilityMeasure (productMeasure M μ θ n)` internally from `hPDF`.
  haveI : ∀ θ : Θ k, ∀ n, IsProbabilityMeasure (productMeasure M μ θ n) :=
    fun θ n => productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- At `h = 0`, `θ₀ + (√n)⁻¹ • 0 = θ₀`, so `_hT_weak 0` gives convergence under `P_θ₀^n`.
  have hT_weak_0 : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (T n)) (L 0) := by
    have h := hT_weak 0
    simp only [smul_zero, add_zero] at h
    exact h
  -- Extract the density normalization and integrability conditions from `hPDF`.
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : Θ k,
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : Θ k,
      Integrable (M.density (θ₀ + t • u)) μ :=
    fun t u => hPDF.density_integrable (θ₀ + t • u)
  -- Internally derive `hScoreCLT`: Δ_n ⇝ multivariateGaussian 0 J under `P^n_{θ₀}` via
  -- `scoreSum_weakly_converges` = `clt_finDim` + iid bridge + score_mean_zero +
  -- dqm_fisher_integrable.
  have hScoreCLT : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint h_one_perturb hint_perturb
      hDQM J hJ_pd.posSemidef hJ
  -- Step 1: `Δ_n` converges weakly to `multivariateGaussian 0 J` under `P^n_{θ₀}`.
  -- `limit_law_under_h` derives the asymptotic comparison from `hDQM` and `hPDF`.
  have h_Δ_tight := score_clt_local M μ θ₀ ℓ hℓ hDQM J hJ hScoreCLT
  -- Step 2: extract a joint subsequence `φ` with limit `π`.
  obtain ⟨φ, hφ_mono, π, hπ_prob, h_joint⟩ :=
    joint_weak_subsequence M μ θ₀ ℓ hℓ T hT_meas (L 0) hT_weak_0
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) h_Δ_tight
  -- **π's second marginal is `multivariateGaussian 0 J`**, by continuous-mapping
  -- applied to the joint weak limit + weak-limit uniqueness against `hScoreCLT`
  -- pulled along `φ`.
  have h_Δ_meas : ∀ n, Measurable (scoreSum ℓ n) := by
    intro n
    unfold scoreSum
    have h_sum : Measurable (fun ω : Fin n → 𝓧 => ∑ i, ℓ (ω i)) :=
      Finset.univ.measurable_sum (fun i _ => hℓ.comp (measurable_pi_apply i))
    exact h_sum.const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have h_π_snd : π.map Prod.snd =
      ProbabilityTheory.multivariateGaussian (0 : Θ k) J := by
    -- Each joint's second marginal is the scoreSum pushforward.
    have h_marg : ∀ k_idx,
        ((productMeasure M μ θ₀ (φ k_idx)).map
            (fun ω => (T (φ k_idx) ω, scoreSum ℓ (φ k_idx) ω))).map Prod.snd
          = (productMeasure M μ θ₀ (φ k_idx)).map (scoreSum ℓ (φ k_idx)) := by
      intro k_idx
      rw [Measure.map_map measurable_snd
        ((hT_meas (φ k_idx)).prodMk (h_Δ_meas (φ k_idx)))]
      rfl
    have hν : WeakConverges
        (fun k_idx => ((productMeasure M μ θ₀ (φ k_idx)).map
          (fun ω => (T (φ k_idx) ω, scoreSum ℓ (φ k_idx) ω))).map Prod.snd)
        (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) := by
      simp_rw [h_marg]
      exact hScoreCLT.comp hφ_mono
    exact WeakConverges.snd_eq h_joint hν
  -- The kernel claimed by the theorem is the conditional distribution
  -- of the first coordinate of `π` given the second, **pre-composed with the
  -- matrix J** (so that it correctly consumes Gaussian-shift draws `x ∼ N(h, J⁻¹)`,
  -- since `J x ∼ N(J h, J)` matches the second-marginal scale of `π`).
  -- Internally derive `vLog` + `hLogLik_weak`: the marginal log-likelihood CLT
  -- `logLikelihood ⇝ N(-v/2, v)` where `v = ⟨h, J h⟩_Mat`. Chain: `hScoreCLT` +
  -- continuous mapping under `⟨h, ·⟩` gives `⟨h, Δ_n⟩ ⇝ N(0, v)` (via
  -- `multivariateGaussian_map_inner_eq_gaussianReal`); affine shift by `-v/2` gives
  -- `⟨h, Δ_n⟩ - v/2 ⇝ N(-v/2, v)`; Slutsky with the LAN residual transports to
  -- `logLikelihood`.
  let vLog : Θ k → NNReal := fun h' =>
    (h'.ofLp ⬝ᵥ J.mulVec h'.ofLp).toNNReal
  have h_vLog_coe : ∀ h' : Θ k,
      (vLog h' : ℝ) = h'.ofLp ⬝ᵥ J.mulVec h'.ofLp := by
    intro h'
    have h_nn : 0 ≤ h'.ofLp ⬝ᵥ J.mulVec h'.ofLp := by
      have := hJ_pd.posSemidef.re_dotProduct_nonneg (x := (h'.ofLp : Fin k → ℝ))
      simpa using this
    exact Real.coe_toNNReal _ h_nn
  have h_vLog_eq_fisher : ∀ h' : Θ k,
      (vLog h' : ℝ)
        = ⟪h', (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h'))⟫ := by
    intro h'
    rw [h_vLog_coe]
    -- Bridge via `Matrix.inner_toEuclideanCLM`: for `x y : EuclideanSpace`,
    -- `⟪x, (toEuclideanCLM A) y⟫ = x.ofLp ⬝ᵥ A.mulVec y.ofLp`; and
    -- `(toEuclideanCLM J) h'` is defeq to `(WithLp.equiv 2 _).symm (J.mulVec h'.ofLp)`.
    change _ = inner ℝ h' ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h')
    rw [Matrix.inner_toEuclideanCLM]
  have hLogLik_weak : ∀ h' : Θ k,
      WeakConverges
        (fun n => (productMeasure M μ θ₀ n).map (logLikelihood M θ₀ h' n))
        (ProbabilityTheory.gaussianReal (-(vLog h' : ℝ) / 2) (vLog h')) := by
    intro h'
    have h_inner_cont : Continuous (fun v : Θ k => ⟪h', v⟫) :=
      continuous_const.inner continuous_id
    have h_inner_meas : Measurable (fun v : Θ k => ⟪h', v⟫) :=
      h_inner_cont.measurable
    have h_Δ_meas_loc : ∀ n, Measurable (scoreSum ℓ n) := by
      intro n
      unfold scoreSum
      exact (Finset.univ.measurable_sum
        (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
        ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
    -- Step A: `⟨h', Δ_n⟩ ⇝ gaussianReal 0 (vLog h')`.
    have h_compA : (fun n => (productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', scoreSum ℓ n ω⟫))
        = (fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
            (fun v : Θ k => ⟪h', v⟫)) := by
      funext n
      exact (Measure.map_map h_inner_meas (h_Δ_meas_loc n)).symm
    have h_scalarCLT : WeakConverges
        (fun n => (productMeasure M μ θ₀ n).map (fun ω => ⟪h', scoreSum ℓ n ω⟫))
        (ProbabilityTheory.gaussianReal 0 (vLog h')) := by
      rw [h_compA]
      have h_map := hScoreCLT.map h_inner_cont h_inner_meas
      rwa [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal h'
        hJ_pd.posSemidef] at h_map
    -- Step B: Shift by `-(vLog h'/2)`.
    have h_sub_cont : Continuous (fun y : ℝ => y - (vLog h' : ℝ) / 2) := by fun_prop
    have h_sub_meas : Measurable (fun y : ℝ => y - (vLog h' : ℝ) / 2) :=
      h_sub_cont.measurable
    have h_compB : (fun n => (productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2))
        = (fun n => ((productMeasure M μ θ₀ n).map
            (fun ω => ⟪h', scoreSum ℓ n ω⟫)).map (fun y : ℝ => y - (vLog h' : ℝ) / 2)) := by
      funext n
      exact (Measure.map_map h_sub_meas
        (h_inner_meas.comp (h_Δ_meas_loc n))).symm
    have h_shiftedCLT : WeakConverges
        (fun n => (productMeasure M μ θ₀ n).map
          (fun ω => ⟪h', scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2))
        (ProbabilityTheory.gaussianReal (-(vLog h' : ℝ) / 2) (vLog h')) := by
      rw [h_compB]
      have h_map := h_scalarCLT.map h_sub_cont h_sub_meas
      rw [ProbabilityTheory.gaussianReal_map_sub_const ((vLog h' : ℝ) / 2),
        zero_sub, ← neg_div] at h_map
      exact h_map
    -- Step C: Slutsky with the LAN residual.
    have h_resid := lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ h'
    -- Match `(vLog h')/2 = (1/2) · ⟪h', Jh'⟩_Mat` so the LAN-residual set aligns
    -- with the `dist (X_n, Y_n)` set from Slutsky.
    have hc_as_fisher :
        (vLog h' : ℝ) / 2 = (1/2 : ℝ) *
          ⟪h', (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h'))⟫ := by
      rw [← h_vLog_eq_fisher]; ring
    -- Aemeasurabilities for Slutsky.
    have hX_ae : ∀ n, AEMeasurable
        (fun ω : Fin n → 𝓧 => ⟪h', scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
        (productMeasure M μ θ₀ n) := fun n =>
      ((h_inner_meas.comp (h_Δ_meas_loc n)).sub_const _).aemeasurable
    have hY_ae : ∀ n, AEMeasurable (logLikelihood M θ₀ h' n)
        (productMeasure M μ θ₀ n) := fun n =>
      (logLikelihood_measurable M θ₀ h' n).aemeasurable
    -- Aligned dist set.
    have h_dist_tendsto : ∀ ε > 0, Tendsto
        (fun n => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε ≤ dist (⟪h', scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
              (logLikelihood M θ₀ h' n ω)})
        atTop (𝓝 0) := by
      intro ε hε
      have h_set_eq : ∀ n,
          {ω : Fin n → 𝓧 | ε ≤ dist (⟪h', scoreSum ℓ n ω⟫ - (vLog h' : ℝ) / 2)
              (logLikelihood M θ₀ h' n ω)}
            = {ω | ε ≤ |logLikelihood M θ₀ h' n ω
                - (⟪h', scoreSum ℓ n ω⟫ - (1/2 : ℝ) *
                    ⟪h', (WithLp.equiv 2 _).symm
                      (J.mulVec ((WithLp.equiv 2 _) h'))⟫)|} := by
        intro n
        ext ω
        simp only [Set.mem_setOf_eq, Real.dist_eq, hc_as_fisher]
        rw [abs_sub_comm]
      simp_rw [h_set_eq]
      exact h_resid ε hε
    exact WeakConverges.slutsky_of_tendstoInMeasure_dist
      hX_ae hY_ae h_shiftedCLT h_dist_tendsto
  -- End of `vLog` / `hLogLik_weak` internal derivation.
  refine ⟨representationKernel J π, inferInstance, ?_⟩
  intro h
  -- Derive `hSlutsky` via `slutsky_bridge_of_lanResidual` and
  -- `lanResidual_tendsto_productMeasure` (LAN_expansion_iii transported from abstract
  -- iid `Ω = ℕ → 𝓧` to `productMeasure`).
  have h_lanResidual_full :=
    lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ h
  have h_lanResidual_subseq : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k_idx => (productMeasure M μ θ₀ (φ k_idx)).real
        {ω : Fin (φ k_idx) → 𝓧 | ε ≤ |logLikelihood M θ₀ h (φ k_idx) ω
                 - (⟪h, scoreSum ℓ (φ k_idx) ω⟫ - (1/2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|})
        atTop (𝓝 0) := fun ε hε =>
    (h_lanResidual_full ε hε).comp hφ_mono.tendsto_atTop
  have hSlutsky_π := slutsky_bridge_of_lanResidual M μ θ₀ ℓ hℓ J T hT_meas h π φ
    (fun n => logLikelihood_measurable M θ₀ h n) h_lanResidual_subseq
  -- Obtain joint weak convergence with the log-likelihood ratio along the same `φ`.
  have h_joint_log := joint_weak_with_logLikelihood
    M μ θ₀ ℓ hℓ hDQM J hJ T hT_meas h π φ hφ_mono h_joint hSlutsky_π
  -- Mutual contiguity `P^n_θ₀ ⊲⊳ P^n_{θ₀+h/√n}` need not be materialized here:
  -- the tilted-law argument consumes log-normal weak convergence directly. Use the
  -- marginal identity `π.map snd = multivariateGaussian 0 J` and the MGF lemmas.
  have h_mgfTilt_integrable := ProbabilityTheory.integrable_exp_tilt
    π J hJ_pd.posSemidef h_π_snd h
  have h_mgfTilt_integral_one := ProbabilityTheory.integral_exp_tilt_eq_one
    π J hJ_pd.posSemidef h_π_snd h
  -- Identify `L_h = Measure.map Prod.fst (π.withDensity (exp ∘ tilt))`.
  have h_L_h_formula := limit_law_under_h
    M μ θ₀ ℓ hℓ hDQM hPDF J hJ_pd T hT_meas h π (L h) (hT_weak h)
    φ hφ_mono h_joint_log
    (fun n => logLikelihood_measurable M θ₀ h n)
    (vLog h) (hLogLik_weak h)
    h_mgfTilt_integrable h_mgfTilt_integral_one
  -- the multivariate Girsanov / Esscher identity in `ForMathlib/GaussianMGF.lean`
  -- gives `HasTiltedLinearPushforward gauss (multivariateGaussian 0 J) J` directly;
  -- transport along `h_π_snd` to get it at the concrete `π.map snd`.
  have hTilt_π : GaussianShift.HasTiltedLinearPushforward gauss (π.map Prod.snd) J := by
    rw [h_π_snd]
    exact GaussianShift.hasTiltedLinearPushforward_of_isGaussianShift hJ_pd hGauss
  -- Rewrite the tilted-law formula as `(gauss h).bind κ`.
  exact gaussianShift_bind_eq_limit J hJ_pd gauss hGauss π h (L h) hTilt_π h_L_h_formula

/-! ## Main theorem: `LAN_representation` (vdV §7.10, kernel form)

Specialises `LAN_representation_of_gaussianShift` to the concrete Gaussian family
`multivariateGaussian h J⁻¹`, matching van der Vaart's statement:

> Under DQM at `θ₀`, non-singular Fisher information `J`, and weak convergence
> `T_n ⇝ L_h` under each `P^n_{θ₀ + h/√n}`, there exists a Markov kernel `κ`
> such that `L_h = N(h, J⁻¹) >>= κ` for every `h`.

The LAN/Le Cam transfer routes through DQM-derived asymptotic singular-mass control
rather than an exact change-of-measure identity, so no common-support assumption is
needed. -/
theorem LAN_representation
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : Θ k → Measure (𝓨 d)) [∀ h, IsProbabilityMeasure (L h)]
    (hT_weak : ∀ h : Θ k,
      WeakConverges
        (fun n => (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map (T n)) (L h))
    [StandardBorelSpace (𝓨 d)] [Nonempty (𝓨 d)]
    [HasOuterApproxClosed (𝓨 d)] [BorelSpace (𝓨 d)]
    (hPDF : IsPDFOf M μ) :
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k, L h = (ProbabilityTheory.multivariateGaussian h J⁻¹).bind κ :=
  LAN_representation_of_gaussianShift M μ θ₀ ℓ hℓ hDQM J hJ_pd hJ T hT_meas L hT_weak
    (fun h => ProbabilityTheory.multivariateGaussian h J⁻¹)
    (GaussianShift.isGaussianShift_multivariateGaussian J⁻¹ hJ_pd.inv)
    hPDF

/-- Equivalent name for `LAN_representation`. -/
theorem LAN_representation_vdV
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : Matrix.PosDef J)
    (hJ : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : Θ k → Measure (𝓨 d)) [∀ h, IsProbabilityMeasure (L h)]
    (hT_weak : ∀ h : Θ k,
      WeakConverges
        (fun n => (productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n).map (T n)) (L h))
    [StandardBorelSpace (𝓨 d)] [Nonempty (𝓨 d)]
    [HasOuterApproxClosed (𝓨 d)] [BorelSpace (𝓨 d)]
    (hPDF : IsPDFOf M μ) :
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k, L h = (ProbabilityTheory.multivariateGaussian h J⁻¹).bind κ :=
  LAN_representation M μ θ₀ ℓ hℓ hDQM J hJ_pd hJ T hT_meas L hT_weak hPDF

end AsymptoticRepresentation
end AsymptoticStatistics
