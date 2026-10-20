module
public import StatLean.Bayesian.BernsteinVonMises.MixtureContiguity
public import StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianDensity
public import StatLean.Bayesian.Dominated.PosteriorLintegral
public import StatLean.Bayesian.Updating.IID

@[expose] public section

/-!
# Step B: Gaussian approximation of the conditioned local posterior

The second half of the proof of the Bernstein–von Mises theorem: on every **fixed** ball `C = B̄(0,
R)` of
the local parameter, the total-variation distance between the `C`-conditioned local
posterior and the `C`-conditioned Gaussian `N(Δ_{n,θ₀}, J⁻¹)` tends to zero in
`P^n_{θ₀}`-probability.

Objects (all with the Lebesgue-density normalizations *dropped* — only ratios matter):

* `bvmJointDens` — the unnormalized local joint density
  `h ↦ ∏ᵢ p_{θ₀+h/√n}(ωᵢ) · f(θ₀+h/√n)` (likelihood times prior density in local
  coordinates; the Jacobian `n^{-k/2}` cancels in all ratios);
* `bvmNumer` — its integral over a set of local parameters;
* `bvmGaussDens` — the unnormalized Gaussian density
  `h ↦ exp(⟪h, Δ̃ₙ⟫ − ⟪h, Jh⟫/2)` with `Δ̃ₙ = scoreSum` (so that `J·Δ_{n,θ₀} = Δ̃ₙ`);
* `bvmLogRatio` — the log of vdV's pair ratio
  `[p_{n,g} π_n(g) / p_{n,h} π_n(h)] / [dN(Δₙ,J⁻¹)(g)/dN(Δₙ,J⁻¹)(h)]`.

Main statements:

* `cond_bvmLocalPosterior_apply_ae` — the conditioned local posterior as a ratio of
  `bvmNumer`s (predictive-a.e., once the rescaled ball sits inside the prior's
  absolute-continuity zone);
* `cond_bvmGaussian_apply` — the conditioned Gaussian as a ratio of `bvmGaussDens`
  integrals;
* `bvmLogRatio_tendsto` — for **fixed** `g, h`, the log pair ratio tends to zero in
  `P^n_{θ₀}`-probability (two applications of the LAN residual + continuity of the prior
  density at `θ₀`); no uniformity in `(g,h)` is needed;
* `local_tv_tendsto` — the Step-B conclusion, for every fixed radius `R`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, pp. 142–143 (the second step, from "Next consider the posterior measures
relative to the priors `Π_n^C`").

**Proof formalization notes.** The chain: `tvDist_normalize_le_double_lintegral` (the
pair-ratio Jensen bound) reduces the conditioned TV distance to a double integral of
`(1 − exp(bvmLogRatio))⁺`; the third measure is replaced by normalized Lebesgue on `C`
through the two-sided Gaussian/Lebesgue comparisons of `MultivariateGaussianDensity` on the
event `‖Δₙ‖ ≤ K` (score-CLT tightness); per-(g,h) convergence (`bvmLogRatio_tendsto`)
lifts to the triple product by Fubini and bounded convergence; the resulting expectation
under the mixture transfers to `P^n_{θ₀}` by `mutuallyContiguous_mixture_base`. The good
events where the a.e. density identities hold are discharged by
`measure_tendsto_zero_of_predictive_null`. Everything is phrased with the **true product
densities** `∏ᵢ p_θ(ωᵢ)` (never `exp ∘ logLikelihood`, which differs off the common-support
rectangle); the LAN residual enters only through `bvmLogRatio_tendsto`, whose proof
restricts to the good rectangle using the DQM singular-mass controls
(`dqm_perturbation_excess/deficit_mass_tendsto`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum logLikelihood)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- The **unnormalized local joint density** at local parameter `h`:
`∏ᵢ p_{θ₀+h/√n}(ωᵢ) · f(θ₀ + h/√n)` (vdV p. 141: `p_{n,h}(x) πₙ(h)`, with the constant
Jacobian dropped). -/
noncomputable def bvmJointDens (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (h : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  (∏ i, ENNReal.ofReal (M.density (bvmLocalUnscale θ₀ n h) (ω i)))
    * ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h))

/-- The **local numerator**: the integral of the local joint density over a set `C` of local
parameters, against Lebesgue measure. -/
noncomputable def bvmNumer (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (C : Set (EuclideanSpace ℝ (Fin k))) (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  ∫⁻ h in C, bvmJointDens M f θ₀ n h ω ∂volume

lemma measurable_bvmNumer
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- LEAN-ONLY: measurable prior density (regularity)
    (hf : Measurable f) (n : ℕ) {C : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable localization set (regularity)
    (hC : MeasurableSet C) :
    Measurable fun ω : Fin n → 𝓧 => bvmNumer M f θ₀ n C ω := by
  have hun : Measurable fun hh : EuclideanSpace ℝ (Fin k) => bvmLocalUnscale θ₀ n hh :=
    measurable_bvmLocalUnscale θ₀ n
  have hjoint : Measurable fun p : (Fin n → 𝓧) × EuclideanSpace ℝ (Fin k) =>
      bvmJointDens M f θ₀ n p.2 p.1 := by
    unfold bvmJointDens
    refine Measurable.mul ?_ ?_
    · refine Finset.univ.measurable_prod fun i _ => ?_
      exact ENNReal.measurable_ofReal.comp
        (hM_joint.comp ((hun.comp measurable_snd).prodMk
          ((measurable_pi_apply i).comp measurable_fst)))
    · exact ENNReal.measurable_ofReal.comp (hf.comp (hun.comp measurable_snd))
  unfold bvmNumer
  exact hjoint.lintegral_prod_right' (ν := volume.restrict C)

/-- The **unnormalized Gaussian density** of `N(Δ_{n,θ₀}, J⁻¹)` in local coordinates:
`exp(⟪h, Δ̃ₙ(ω)⟫ − ⟪h, Jh⟫/2)` with `Δ̃ₙ = scoreSum` (note `J Δ_{n,θ₀} = Δ̃ₙ`; the
Lebesgue normalizer and the factor `exp(−⟪Δₙ, JΔₙ⟫/2)` are dropped — they cancel in
ratios). -/
noncomputable def bvmGaussDens (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (h : EuclideanSpace ℝ (Fin k))
    (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (⟪h, scoreSum sc n ω⟫
    - (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))

-- The unnormalized Gaussian density is measurable in the local parameter.
private lemma measurable_bvmGaussDens (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    Measurable fun h : EuclideanSpace ℝ (Fin k) => bvmGaussDens J sc n h ω := by
  have hcont : Continuous fun h : EuclideanSpace ℝ (Fin k) =>
      (⟪h, scoreSum sc n ω⟫ - (1 / 2 : ℝ) * ⟪h, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) h⟫) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hcont).measurable

-- A positive finite scalar cancels between the two `cond` factors.
private lemma ennreal_smul_cond_ratio {d X Y : ℝ≥0∞} (hd : d ≠ 0) (hd' : d ≠ ∞) :
    (d * X)⁻¹ * (d * Y) = Y / X := by
  rw [ENNReal.mul_inv (Or.inl hd) (Or.inl hd'), div_eq_mul_inv,
    show d⁻¹ * X⁻¹ * (d * Y) = (d⁻¹ * d) * (Y * X⁻¹) from by ring,
    ENNReal.inv_mul_cancel hd hd', one_mul]

/-- The random Gaussian `N(Δₙ, J⁻¹)` is a positive finite multiple of the Lebesgue measure
with density `bvmGaussDens`: the normalizer and the mean-dependent constant of the tilt are
absorbed into the scalar, which then cancels in every conditional ratio. -/
private lemma exists_bvmGaussian_eq_smul_withDensity (hJ_pd : J.PosDef) (n : ℕ)
    (ω : Fin n → 𝓧) :
    ∃ d : ℝ≥0∞, 0 < d ∧ d ≠ ∞ ∧
      bvmGaussian J sc n ω
        = d • volume.withDensity fun h => bvmGaussDens J sc n h ω := by
  classical
  have hJunit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ_pd.isUnit
  have hS : (J⁻¹).PosDef := hJ_pd.inv
  have hSS : (J⁻¹)⁻¹ = J := Matrix.nonsing_inv_nonsing_inv _ hJunit
  -- `J Δₙ = scoreSum`, since `Δₙ = J⁻¹ scoreSum`
  have hJm : (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (bvmEffScore J sc n ω) = scoreSum sc n ω := by
    rw [bvmEffScore, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      ← map_mul, Matrix.mul_nonsing_inv _ hJunit, map_one]
    rfl
  obtain ⟨c, hcpos, hctop, hc⟩ := AsymptoticStatistics.multivariateGaussian_eq_smul_withDensity hS
  have htilt := AsymptoticStatistics.multivariateGaussian_eq_withDensity_tilt hS
    (bvmEffScore J sc n ω)
  rw [hSS] at hc htilt
  rw [hJm] at htilt
  set a : ℝ := ⟪bvmEffScore J sc n ω, scoreSum sc n ω⟫ with ha
  have hD0meas : Measurable fun x : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ / 2)) := by
    have : Continuous fun x : EuclideanSpace ℝ (Fin k) =>
        (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ / 2) := by fun_prop
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp this).measurable
  have hD1meas : Measurable fun y : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (Real.exp (⟪scoreSum sc n ω, y⟫ - a / 2)) := by
    have : Continuous fun y : EuclideanSpace ℝ (Fin k) =>
        (⟪scoreSum sc n ω, y⟫ - a / 2) := by fun_prop
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp this).measurable
  have hGmeas := measurable_bvmGaussDens J sc n ω
  have hprod : ((fun x : EuclideanSpace ℝ (Fin k) =>
        ENNReal.ofReal (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ / 2)))
      * fun y : EuclideanSpace ℝ (Fin k) =>
        ENNReal.ofReal (Real.exp (⟪scoreSum sc n ω, y⟫ - a / 2)))
      = ENNReal.ofReal (Real.exp (-a / 2)) • fun x => bvmGaussDens J sc n x ω := by
    funext x
    have hq : ⟪x, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) x))⟫
        = ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ := rfl
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, bvmGaussDens]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hq, real_inner_comm (scoreSum sc n ω) x]
    ring_nf
  refine ⟨c * ENNReal.ofReal (Real.exp (-a / 2)), ?_, ?_, ?_⟩
  · exact ENNReal.mul_pos hcpos.ne' (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  · exact ENNReal.mul_ne_top hctop ENNReal.ofReal_ne_top
  · rw [bvmGaussian, htilt, hc, withDensity_smul_measure,
      ← withDensity_mul _ hD0meas hD1meas, hprod, withDensity_smul _ hGmeas, smul_smul]

/-- **The conditioned Gaussian as a density ratio**: for positive definite `J`,
`(N(Δₙ, J⁻¹))[|C] A = (∫_{A∩C} bvmGaussDens dλ) / (∫_C bvmGaussDens dλ)`. -/
theorem cond_bvmGaussian_apply
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef) (n : ℕ) (ω : Fin n → 𝓧)
    {C A : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable localization and target sets (regularity)
    (hC : MeasurableSet C) (hA : MeasurableSet A) :
    ((bvmGaussian J sc n ω)[|C]) A
      = (∫⁻ h in A ∩ C, bvmGaussDens J sc n h ω ∂volume)
          / ∫⁻ h in C, bvmGaussDens J sc n h ω ∂volume := by
  obtain ⟨d, hdpos, hdtop, hd⟩ := exists_bvmGaussian_eq_smul_withDensity (sc := sc) hJ_pd n ω
  have hGmeas := measurable_bvmGaussDens J sc n ω
  rw [ProbabilityTheory.cond_apply hC, hd, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, withDensity_apply _ hC, withDensity_apply _ (hC.inter hA),
    Set.inter_comm C A, ennreal_smul_cond_ratio hdpos.ne' hdtop]

/-- **First display of vdV p. 143, Gaussian side**: the `C`-conditioned Gaussian is exactly
the normalized `bvmGaussDens` density against Lebesgue measure on `C` — the shape consumed by
`tvDist_normalize_le_double_lintegral`. -/
private lemma cond_bvmGaussian_eq_withDensity (hJ_pd : J.PosDef) (n : ℕ) (ω : Fin n → 𝓧)
    {C : Set (EuclideanSpace ℝ (Fin k))} (hC : MeasurableSet C) :
    ((bvmGaussian J sc n ω)[|C])
      = (volume.restrict C).withDensity fun h =>
          bvmGaussDens J sc n h ω / ∫⁻ y in C, bvmGaussDens J sc n y ω ∂volume := by
  have hGmeas := measurable_bvmGaussDens J sc n ω
  ext A hA
  rw [cond_bvmGaussian_apply hJ_pd n ω hC hA, withDensity_apply _ hA,
    Measure.restrict_restrict hA]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hGmeas.aemeasurable]

-- LEAN-ONLY affine change of variables `θ = θ₀ + h/√n` on a rescaled set: the Jacobian is the
-- constant `(√n)^{-k}` (`k = dim`).
private lemma lintegral_preimage_bvmLocalScale (θ₀ : EuclideanSpace ℝ (Fin k)) {n : ℕ}
    (hn1 : 1 ≤ n) {D : Set (EuclideanSpace ℝ (Fin k))} (hD : MeasurableSet D)
    {G : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ θ in bvmLocalScale θ₀ n ⁻¹' D, G θ
      = ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k)
          * ∫⁻ hh in D, G (bvmLocalUnscale θ₀ n hh) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set a : ℝ := (Real.sqrt n)⁻¹ with hadef
  have hapos : 0 < a := by rw [hadef]; exact inv_pos.mpr (Real.sqrt_pos.mpr hnpos)
  set T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := bvmLocalUnscale θ₀ n with hT
  have hTmeas : Measurable T := measurable_bvmLocalUnscale θ₀ n
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have hmap : Measure.map T (volume : Measure (EuclideanSpace ℝ (Fin k)))
      = ENNReal.ofReal ((a ^ k)⁻¹) • (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
    have h1 : Measure.map (fun hh : EuclideanSpace ℝ (Fin k) => a • hh) volume
        = ENNReal.ofReal |(a ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))))⁻¹|
            • (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
      Measure.map_addHaar_smul volume hapos.ne'
    have h2 : T = (fun y : EuclideanSpace ℝ (Fin k) => θ₀ + y)
        ∘ (fun hh : EuclideanSpace ℝ (Fin k) => a • hh) := by
      funext hh; simp [hT, bvmLocalUnscale, hadef]
    rw [h2, ← Measure.map_map (measurable_const_add θ₀) (measurable_const_smul a), h1,
      Measure.map_smul, Measure.IsAddLeftInvariant.map_add_left_eq_self
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin k)))) θ₀]
    rw [hfr, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a ^ k)⁻¹)]
  have hpre : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' D) := (measurable_bvmLocalScale θ₀ n) hD
  have hmem : ∀ hh, (T hh ∈ bvmLocalScale θ₀ n ⁻¹' D) ↔ hh ∈ D := by
    intro hh
    simp only [Set.mem_preimage, hT, bvmLocalScale_bvmLocalUnscale θ₀ hn1 hh]
  have hind : ∀ hh, (bvmLocalScale θ₀ n ⁻¹' D).indicator G (T hh)
      = D.indicator (fun y => G (T y)) hh := by
    intro hh
    by_cases hmem' : hh ∈ D
    · rw [Set.indicator_of_mem ((hmem hh).mpr hmem'), Set.indicator_of_mem hmem']
    · rw [Set.indicator_of_notMem (fun hc => hmem' ((hmem hh).mp hc)),
        Set.indicator_of_notMem hmem']
  have hkey := (lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin k))))
      (f := (bvmLocalScale θ₀ n ⁻¹' D).indicator G) (g := T)
      (hG.indicator hpre) hTmeas).symm
  rw [hmap, lintegral_smul_measure, lintegral_indicator hpre] at hkey
  simp_rw [hind] at hkey
  rw [lintegral_indicator hD] at hkey
  rw [hkey, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (pow_pos hapos k)),
    mul_inv_cancel₀ (pow_pos hapos k).ne', ENNReal.ofReal_one, one_mul]

-- The `π`-integral of the product likelihood over the rescaled set is the Jacobian times
-- `bvmNumer`: on the rescaled set the prior is `f · volume`, and the affine substitution
-- `θ = θ₀ + h/√n` turns the integrand into `bvmJointDens`.
private lemma lintegral_preimage_eq_jac_mul_bvmNumer
    (hπ : HasLocalDensity π θ₀ r₀ f)
    (hM_joint : Measurable (Function.uncurry M.density)) {n : ℕ} (hn1 : 1 ≤ n)
    {D : Set (EuclideanSpace ℝ (Fin k))} (hD : MeasurableSet D)
    (hDsub : bvmLocalScale θ₀ n ⁻¹' D ⊆ Metric.ball θ₀ r₀) (ω : Fin n → 𝓧) :
    ∫⁻ θ in bvmLocalScale θ₀ n ⁻¹' D, (∏ i, ENNReal.ofReal (M.density θ (ω i))) ∂π
      = ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) * bvmNumer M f θ₀ n D ω := by
  classical
  have hsm : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' D) := (measurable_bvmLocalScale θ₀ n) hD
  have hGmeas : Measurable fun θ : EuclideanSpace ℝ (Fin k) =>
      ∏ i, ENNReal.ofReal (M.density θ (ω i)) := by
    refine Finset.univ.measurable_prod fun i _ => ?_
    exact ENNReal.measurable_ofReal.comp (hM_joint.comp (measurable_id.prodMk measurable_const))
  have hFmeas : Measurable fun θ : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (f θ) :=
    ENNReal.measurable_ofReal.comp hπ.measurable
  have hres : π.restrict (bvmLocalScale θ₀ n ⁻¹' D)
      = (volume.restrict (bvmLocalScale θ₀ n ⁻¹' D)).withDensity
          fun θ => ENNReal.ofReal (f θ) := by
    rw [← Measure.restrict_restrict_of_subset hDsub, hπ.restrict_eq,
      restrict_withDensity hsm, Measure.restrict_restrict_of_subset hDsub]
  rw [hres, lintegral_withDensity_eq_lintegral_mul _ hFmeas hGmeas]
  simp only [Pi.mul_apply]
  rw [lintegral_preimage_bvmLocalScale θ₀ hn1 hD (hFmeas.fun_mul hGmeas)]
  congr 1
  refine lintegral_congr fun hh => ?_
  simp only [bvmJointDens]
  ring

-- The scalar `q` (Jacobian) and the predictive normalizer `Z` cancel in the conditional ratio.
private lemma ennreal_posterior_ratio {q Z X Y : ℝ≥0∞} (hq : q ≠ 0) (hq' : q ≠ ∞)
    (hZ : Z ≠ 0) (hZ' : Z ≠ ∞) :
    ((q * X) / Z)⁻¹ * ((q * Y) / Z) = Y / X := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hZ)) (Or.inr (ENNReal.inv_ne_zero.mpr hZ')),
    ENNReal.mul_inv (Or.inl hq) (Or.inl hq'), inv_inv,
    show q⁻¹ * X⁻¹ * Z * (q * Y * Z⁻¹) = q⁻¹ * q * (Z * Z⁻¹) * (Y * X⁻¹) from by ring,
    ENNReal.inv_mul_cancel hq hq', ENNReal.mul_inv_cancel hZ hZ', one_mul, one_mul]

/-- **The conditioned local posterior as a `bvmNumer` ratio** (predictive-a.e.): once the
rescaled ball `C/√n + θ₀` lies inside the prior's absolute-continuity ball
(`R < r₀ √n`), for predictive-a.e. `ω` with nonvanishing local mass,
`(localPosterior ω)[|C] A = bvmNumer (A∩C) / bvmNumer C`. -/
theorem cond_bvmLocalPosterior_apply_ae
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {R : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hR : 0 < R) {n : ℕ}
    -- LEAN-ONLY: the rescaled ball sits inside the absolute-continuity zone
    (hn : R < r₀ * Real.sqrt n)
    {C A : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable sets, localization inside the radius-`R` ball (regularity)
    (hC : MeasurableSet C) (hCsub : C ⊆ Metric.closedBall 0 R) (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(iidKernel κ n ∘ₘ π), bvmNumer M f θ₀ n C ω ≠ 0 →
      ((bvmLocalPosterior κ π θ₀ n ω)[|C]) A
        = bvmNumer M f θ₀ n (A ∩ C) ω / bvmNumer M f θ₀ n C ω := by
  classical
  have hr₀ : 0 < r₀ := hπ.rad_pos
  have hsqrt : 0 < Real.sqrt n := by
    rcases le_or_gt (Real.sqrt n) 0 with hle | hlt
    · exact absurd hn (by nlinarith)
    · exact hlt
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · subst h0; simp at hsqrt
    · exact h1
  -- The rescaled sets sit inside the prior's absolute-continuity ball.
  have hsub : ∀ D : Set (EuclideanSpace ℝ (Fin k)), D ⊆ Metric.closedBall 0 R →
      bvmLocalScale θ₀ n ⁻¹' D ⊆ Metric.ball θ₀ r₀ := by
    intro D hD θ hθ
    have h1 : bvmLocalScale θ₀ n θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R :=
      hD hθ
    rw [Metric.mem_closedBall, dist_zero_right, bvmLocalScale, norm_smul, Real.norm_eq_abs,
      abs_of_pos hsqrt] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : Real.sqrt n * ‖θ - θ₀‖ < Real.sqrt n * r₀ :=
      lt_of_le_of_lt h1 (by rw [mul_comm]; exact hn)
    exact lt_of_mul_lt_mul_left h2 hsqrt.le
  -- The dominated iid experiment, in `withDensity` form.
  have hdens_meas : Measurable
      (Function.uncurry fun θ (x : 𝓧) => ENNReal.ofReal (M.density θ x)) :=
    ENNReal.measurable_ofReal.comp hM_joint
  have hP : Measurable (Function.uncurry
      fun (θ : EuclideanSpace ℝ (Fin k)) (x : Fin n → 𝓧) =>
        ∏ i, ENNReal.ofReal (M.density θ (x i))) :=
    measurable_uncurry_prod_likelihood hdens_meas
  have hκ' : ∀ θ, iidKernel κ n θ
      = (Measure.pi fun _ : Fin n => μ).withDensity
          fun x => ∏ i, ENNReal.ofReal (M.density θ (x i)) :=
    fun θ => iidKernel_withDensity hdens_meas hκ n θ
  have hpreC : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' C) := (measurable_bvmLocalScale θ₀ n) hC
  have hpreCA : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' (C ∩ A)) :=
    (measurable_bvmLocalScale θ₀ n) (hC.inter hA)
  filter_upwards [posterior_apply_eq_div (π := π) hP hκ' hpreC,
    posterior_apply_eq_div (π := π) hP hκ' hpreCA,
    posterior_apply_eq_div (π := π) hP hκ' (MeasurableSet.univ
      (α := EuclideanSpace ℝ (Fin k)))] with ω hωC hωCA hωU _
  -- The predictive normalizer is positive and finite, since the posterior is Markov.
  have hZ1 : (∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π)
      / ∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π = 1 := by
    have h := hωU
    simp only [Measure.restrict_univ, measure_univ] at h
    exact h.symm
  have hZne : (∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π) ≠ 0 := by
    intro h0; rw [h0] at hZ1; simp at hZ1
  have hZtop : (∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π) ≠ ∞ := by
    intro h0; rw [h0] at hZ1; simp at hZ1
  -- The Jacobian scalar.
  have hqpos : (0 : ℝ) < ((Real.sqrt n)⁻¹) ^ k := by positivity
  have hq : ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  -- Push the conditioning through the rescaling map.
  have hmap : ∀ S : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet S →
      bvmLocalPosterior κ π θ₀ n ω S
        = ((iidKernel κ n)†π) ω (bvmLocalScale θ₀ n ⁻¹' S) := by
    intro S hS
    rw [bvmLocalPosterior, Kernel.map_apply' _ (measurable_bvmLocalScale θ₀ n) _ hS]
  rw [ProbabilityTheory.cond_apply hC, hmap C hC, hmap (C ∩ A) (hC.inter hA), hωC, hωCA,
    lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 hC (hsub C hCsub) ω,
    lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 (hC.inter hA)
      (hsub (C ∩ A) (Set.inter_subset_left.trans hCsub)) ω,
    Set.inter_comm C A, ennreal_posterior_ratio hq ENNReal.ofReal_ne_top hZne hZtop]

/-- **The log pair ratio** of vdV p. 143: the logarithm of
`[p_{n,g} πₙ(g) / p_{n,h} πₙ(h)] · [dN(Δₙ,J⁻¹)(h) / dN(Δₙ,J⁻¹)(g)]`, i.e.
`(Lₙ(g) − Lₙ(h)) + (log f(θ₀+g/√n) − log f(θ₀+h/√n))
  − (⟪g − h, Δ̃ₙ⟫ − ⟪g,Jg⟫/2 + ⟪h,Jh⟫/2)`. -/
noncomputable def bvmLogRatio (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ) (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (g h : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) : ℝ :=
  (logLikelihood M θ₀ g n ω - logLikelihood M θ₀ h n ω)
    + (Real.log (f (bvmLocalUnscale θ₀ n g)) - Real.log (f (bvmLocalUnscale θ₀ n h)))
    - (⟪g - h, scoreSum sc n ω⟫
        - (1 / 2 : ℝ) * ⟪g, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) g))⟫
        + (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)

/-- **Fixed-pair vanishing of the log pair ratio** (vdV p. 143: "the integrand converges to
zero in probability … by Theorem 7.2 and the continuity of `π` at `θ₀`"): for every fixed
`g, h`, the log pair ratio tends to zero in `P^n_{θ₀}`-probability. Two applications of the
LAN residual (`lanResidual_tendsto_productMeasure`) plus the deterministic convergence of
the prior-density log ratio. -/
theorem bvmLogRatio_tendsto
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    (g h : EuclideanSpace ℝ (Fin k)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω | ε ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}) atTop (𝓝 0) := by
  classical
  haveI hProb : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF θ₀ n
  -- The LAN residual at an arbitrary fixed local parameter.
  set res : EuclideanSpace ℝ (Fin k) → ∀ n : ℕ, (Fin n → 𝓧) → ℝ := fun x n ω =>
    logLikelihood M θ₀ x n ω - (⟪x, scoreSum sc n ω⟫ - (1 / 2 : ℝ) *
      ⟪x, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) x))⟫) with hres_def
  have hres : ∀ x : EuclideanSpace ℝ (Fin k), ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |res x n ω|}) atTop (𝓝 0) := fun x =>
    AsymptoticStatistics.AsymptoticRepresentation.lanResidual_tendsto_productMeasure
      M μ θ₀ sc hsc (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀)
      (fun _ _ => hPDF.density_integral_eq_one _) (fun _ _ => hPDF.density_integrable _)
      hDQM J hJ x
  -- The prior log-ratio is deterministic and vanishes, by continuity and positivity at `θ₀`.
  have hunsc : ∀ x : EuclideanSpace ℝ (Fin k),
      Tendsto (fun n : ℕ => bvmLocalUnscale θ₀ n x) atTop (𝓝 θ₀) := by
    intro x
    have hsq : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hsm : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • x) atTop (𝓝 ((0 : ℝ) • x)) :=
      hsq.smul_const x
    have := tendsto_const_nhds (x := θ₀) (f := (atTop : Filter ℕ)) |>.add hsm
    simpa [bvmLocalUnscale] using this
  have hlog : ∀ x : EuclideanSpace ℝ (Fin k),
      Tendsto (fun n : ℕ => Real.log (f (bvmLocalUnscale θ₀ n x))) atTop
        (𝓝 (Real.log (f θ₀))) := by
    intro x
    exact ((Real.continuousAt_log hπ.pos.ne').comp hπ.continuousAt).tendsto.comp (hunsc x)
  have hpterm : Tendsto (fun n : ℕ =>
      Real.log (f (bvmLocalUnscale θ₀ n g)) - Real.log (f (bvmLocalUnscale θ₀ n h)))
      atTop (𝓝 0) := by simpa using (hlog g).sub (hlog h)
  -- The algebraic decomposition: the two score/quadratic terms recombine exactly.
  have hdecomp : ∀ (n : ℕ) (ω : Fin n → 𝓧),
      bvmLogRatio M f θ₀ J sc n g h ω = res g n ω - res h n ω
        + (Real.log (f (bvmLocalUnscale θ₀ n g))
            - Real.log (f (bvmLocalUnscale θ₀ n h))) := by
    intro n ω
    have hsub : ⟪g - h, scoreSum sc n ω⟫
        = ⟪g, scoreSum sc n ω⟫ - ⟪h, scoreSum sc n ω⟫ := inner_sub_left (𝕜 := ℝ) _ _ _
    simp only [bvmLogRatio, hres_def, hsub]
    ring
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_
    (by simpa using (hres g (ε / 3) hε3).add (hres h (ε / 3) hε3))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpterm (ε / 3) hε3
  filter_upwards [eventually_ge_atTop N] with n hn
  have hincl : {ω : Fin n → 𝓧 | ε ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}
      ⊆ {ω : Fin n → 𝓧 | ε / 3 ≤ |res g n ω|} ∪ {ω : Fin n → 𝓧 | ε / 3 ≤ |res h n ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hp : |Real.log (f (bvmLocalUnscale θ₀ n g))
        - Real.log (f (bvmLocalUnscale θ₀ n h))| < ε / 3 := by
      have := hN n hn
      rwa [Real.dist_eq, sub_zero] at this
    have hb1 : |bvmLogRatio M f θ₀ J sc n g h ω|
        ≤ |res g n ω - res h n ω| + |Real.log (f (bvmLocalUnscale θ₀ n g))
            - Real.log (f (bvmLocalUnscale θ₀ n h))| := by
      rw [hdecomp n ω]; exact abs_add_le _ _
    have hb2 : |res g n ω - res h n ω| ≤ |res g n ω| + |res h n ω| := by
      have := abs_add_le (res g n ω) (-(res h n ω))
      simpa [sub_eq_add_neg] using this
    linarith
  calc (productMeasure M μ θ₀ n).real {ω | ε ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}
      ≤ (productMeasure M μ θ₀ n).real
          ({ω : Fin n → 𝓧 | ε / 3 ≤ |res g n ω|}
            ∪ {ω : Fin n → 𝓧 | ε / 3 ≤ |res h n ω|}) := measureReal_mono hincl
    _ ≤ (productMeasure M μ θ₀ n).real {ω : Fin n → 𝓧 | ε / 3 ≤ |res g n ω|}
          + (productMeasure M μ θ₀ n).real {ω : Fin n → 𝓧 | ε / 3 ≤ |res h n ω|} :=
        measureReal_union_le _ _

/-! ### Step-B bricks -/

-- LEAN-ONLY: the pair-ratio Jensen bound in the form needed here. Unlike
-- `tvDist_normalize_le_double_lintegral` this version does **not** require the first density
-- to be a.e. positive — the local joint density vanishes wherever the model density does —
-- because the scalar Jensen step is applied directly to the antisymmetric numerator
-- `s h * t g − s g * t h`.
private lemma tvDist_normalize_le_double_lintegral_antisymm {α : Type*} [MeasurableSpace α]
    (base : Measure α) {s t : α → ℝ≥0∞} (hs : Measurable s) (ht : Measurable t)
    (hs0 : ∫⁻ y, s y ∂base ≠ 0) (hsT : ∫⁻ y, s y ∂base ≠ ∞)
    (ht0 : ∫⁻ y, t y ∂base ≠ 0) (htT : ∫⁻ y, t y ∂base ≠ ∞) :
    Minimaxity.tvDist (base.withDensity fun x => s x / ∫⁻ y, s y ∂base)
        (base.withDensity fun x => t x / ∫⁻ y, t y ∂base)
      ≤ ((∫⁻ y, s y ∂base) * ∫⁻ y, t y ∂base)⁻¹
          * ∫⁻ h, ∫⁻ g, (s h * t g - s g * t h) ∂base ∂base := by
  classical
  set Zs := ∫⁻ y, s y ∂base with hZs
  set Zt := ∫⁻ y, t y ∂base with hZt
  have hpm : Measurable fun x => s x / Zs := hs.div_const Zs
  have hqm : Measurable fun x => t x / Zt := ht.div_const Zt
  have hmass : ∀ (u : α → ℝ≥0∞) (Z : ℝ≥0∞), Z = ∫⁻ y, u y ∂base → Z ≠ 0 → Z ≠ ∞ →
      ∫⁻ x, u x / Z ∂base = 1 := by
    intro u Z hZ h0 hT
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr h0), ← hZ]
    exact ENNReal.mul_inv_cancel h0 hT
  haveI : IsProbabilityMeasure (base.withDensity fun x => s x / Zs) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hmass s Zs hZs hs0 hsT⟩
  haveI : IsProbabilityMeasure (base.withDensity fun x => t x / Zt) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hmass t Zt hZt ht0 htT⟩
  rw [tvDist_withDensity_eq base hpm hqm]
  have hZ0 : Zs * Zt ≠ 0 := mul_ne_zero hs0 ht0
  have e1 : ∀ x, (Zs * Zt)⁻¹ * (s x * Zt) = s x / Zs := by
    intro x
    rw [ENNReal.mul_inv (Or.inl hs0) (Or.inl hsT), div_eq_mul_inv,
      show Zs⁻¹ * Zt⁻¹ * (s x * Zt) = Zt⁻¹ * Zt * (s x * Zs⁻¹) from by ring,
      ENNReal.inv_mul_cancel ht0 htT, one_mul]
  have e2 : ∀ x, (Zs * Zt)⁻¹ * (t x * Zs) = t x / Zt := by
    intro x
    rw [ENNReal.mul_inv (Or.inl hs0) (Or.inl hsT), div_eq_mul_inv,
      show Zs⁻¹ * Zt⁻¹ * (t x * Zs) = Zs⁻¹ * Zs * (t x * Zt⁻¹) from by ring,
      ENNReal.inv_mul_cancel hs0 hsT, one_mul]
  have key : ∀ x, s x / Zs - t x / Zt = (Zs * Zt)⁻¹ * (s x * Zt - t x * Zs) := by
    intro x
    rw [ENNReal.mul_sub (fun _ _ => ENNReal.inv_ne_top.mpr hZ0), e1, e2]
  simp_rw [key]
  rw [lintegral_const_mul _ ((hs.mul_const Zt).fun_sub (ht.mul_const Zs))]
  refine mul_le_mul_right (lintegral_mono fun x => ?_) _
  have h1 : s x * Zt = ∫⁻ g, s x * t g ∂base := by
    rw [hZt, lintegral_const_mul _ ht]
  have h2 : t x * Zs = ∫⁻ g, s g * t x ∂base := by
    rw [hZs, lintegral_mul_const _ hs, mul_comm]
  rw [h1, h2]
  exact lintegral_sub_le _ _ (hs.mul_const (t x))

-- LEAN-ONLY: two-sided bound on the unnormalized Gaussian density over a ball of radius `R`,
-- in terms of a bound `K` on the score sum.
private lemma bvmGaussDens_bounds (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) {R K : ℝ} (hR : 0 ≤ R) {n : ℕ} {ω : Fin n → 𝓧}
    (hK : ‖scoreSum sc n ω‖ ≤ K) {g : EuclideanSpace ℝ (Fin k)} (hg : ‖g‖ ≤ R) :
    ENNReal.ofReal (Real.exp (-(R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2)))
          ≤ bvmGaussDens J sc n g ω ∧
        bvmGaussDens J sc n g ω
          ≤ ENNReal.ofReal
              (Real.exp (R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2)) := by
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) J with hL
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hK
  have hdens : bvmGaussDens J sc n g ω
      = ENNReal.ofReal (Real.exp (⟪g, scoreSum sc n ω⟫ - (1 / 2 : ℝ) * ⟪g, L g⟫)) := rfl
  have h1 : |⟪g, scoreSum sc n ω⟫| ≤ R * K := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    exact mul_le_mul hg hK (norm_nonneg _) hR
  have h2 : |⟪g, L g⟫| ≤ ‖L‖ * R ^ 2 := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have hLg : ‖L g‖ ≤ ‖L‖ * R :=
      le_trans (L.le_opNorm g) (by exact mul_le_mul_of_nonneg_left hg (norm_nonneg _))
    calc ‖g‖ * ‖L g‖ ≤ R * (‖L‖ * R) :=
          mul_le_mul hg hLg (norm_nonneg _) hR
      _ = ‖L‖ * R ^ 2 := by ring
  have hLR : 0 ≤ ‖L‖ * R ^ 2 := by positivity
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  constructor
  · rw [hdens]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  · rw [hdens]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

-- LEAN-ONLY: the Gaussian normalizer over a fixed ball is positive and finite.
private lemma lintegral_bvmGaussDens_pos (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) {R : ℝ} (hR : 0 < R) (n : ℕ) (ω : Fin n → 𝓧) :
    0 < ∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
        bvmGaussDens J sc n y ω := by
  set b : ℝ := R * ‖scoreSum sc n ω‖ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2 with hb
  have hlow : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
      ENNReal.ofReal (Real.exp (-b)) ≤ bvmGaussDens J sc n y ω := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact (bvmGaussDens_bounds J sc hR.le le_rfl hy).1
  have hmono := setLIntegral_mono_ae (μ := (volume : Measure (EuclideanSpace ℝ (Fin k))))
    (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R)
    (f := fun _ => ENNReal.ofReal (Real.exp (-b)))
    (g := fun y => bvmGaussDens J sc n y ω) (measurable_bvmGaussDens J sc n ω).aemeasurable
    (Filter.Eventually.of_forall hlow)
  refine lt_of_lt_of_le ?_ hmono
  rw [setLIntegral_const]
  refine ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ?_
  exact (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 hR)
    (measure_mono Metric.ball_subset_closedBall)).ne'

private lemma lintegral_bvmGaussDens_ne_top (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) {R : ℝ} (hR : 0 ≤ R) (n : ℕ) (ω : Fin n → 𝓧) :
    (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
        bvmGaussDens J sc n y ω) ≠ ∞ := by
  set b : ℝ := R * ‖scoreSum sc n ω‖ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2 with hb
  have hup : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
      bvmGaussDens J sc n y ω ≤ ENNReal.ofReal (Real.exp b) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact (bvmGaussDens_bounds J sc hR le_rfl hy).2
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_closedBall hup)
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne

-- LEAN-ONLY: on the event `‖scoreSum‖ ≤ K`, the conditioned Gaussian density is bounded by a
-- constant depending only on `(R, K, J)` — the comparison with normalized Lebesgue measure
-- on the ball.
private lemma bvmGaussDens_div_lintegral_le (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) {R K : ℝ} (hR : 0 < R) {n : ℕ} {ω : Fin n → 𝓧}
    (hK : ‖scoreSum sc n ω‖ ≤ K) {g : EuclideanSpace ℝ (Fin k)} (hg : ‖g‖ ≤ R) :
    bvmGaussDens J sc n g ω / (∫⁻ y in Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin k)) R, bvmGaussDens J sc n y ω)
      ≤ ENNReal.ofReal (Real.exp
            (2 * (R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2)))
          / volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) := by
  set b : ℝ := R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2 with hb
  set V := volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) with hV
  have hlow : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
      ENNReal.ofReal (Real.exp (-b)) ≤ bvmGaussDens J sc n y ω := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact (bvmGaussDens_bounds J sc hR.le hK hy).1
  have hTlow : ENNReal.ofReal (Real.exp (-b)) * V
      ≤ ∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
          bvmGaussDens J sc n y ω := by
    have hmono := setLIntegral_mono_ae (μ := (volume : Measure (EuclideanSpace ℝ (Fin k))))
      (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R)
      (f := fun _ => ENNReal.ofReal (Real.exp (-b)))
      (g := fun y => bvmGaussDens J sc n y ω) (measurable_bvmGaussDens J sc n ω).aemeasurable
      (Filter.Eventually.of_forall hlow)
    rwa [setLIntegral_const] at hmono
  have hnum : bvmGaussDens J sc n g ω ≤ ENNReal.ofReal (Real.exp b) :=
    (bvmGaussDens_bounds J sc hR.le hK hg).2
  refine le_trans (ENNReal.div_le_div hnum hTlow) (le_of_eq ?_)
  have hsplit : ENNReal.ofReal (Real.exp b)
      = ENNReal.ofReal (Real.exp (-b)) * ENNReal.ofReal (Real.exp (2 * b)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    ring_nf
  rw [hsplit]
  exact ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    ENNReal.ofReal_ne_top

-- LEAN-ONLY: measure-level form of `cond_bvmLocalPosterior_apply_ae`. The exceptional set is
-- **uniform in the target event** because the input is the measure-level Bayes formula
-- `posterior_iid_eq_withDensity_prod_likelihood` (rather than its set-evaluated corollary),
-- which is what allows the conditioned posterior to be fed to a total-variation bound.
private lemma cond_bvmLocalPosterior_eq_withDensity_ae
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {R : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hR : 0 < R)
    -- LEAN-ONLY: the rescaled ball sits inside the absolute-continuity zone
    {n : ℕ} (hn : R < r₀ * Real.sqrt n) :
    ∀ᵐ ω ∂(iidKernel κ n ∘ₘ π),
      bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω ≠ 0 →
        ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin k)) R])
          = (volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R)).withDensity
              fun h => bvmJointDens M f θ₀ n h ω
                / bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω := by
  classical
  have hsqrt : 0 < Real.sqrt n := by
    rcases le_or_gt (Real.sqrt n) 0 with hle | hlt
    · exact absurd hn (by nlinarith [hπ.rad_pos])
    · exact hlt
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · subst h0; simp at hsqrt
    · exact h1
  set C : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall 0 R with hCdef
  have hC : MeasurableSet C := measurableSet_closedBall
  have hsub : ∀ D : Set (EuclideanSpace ℝ (Fin k)), D ⊆ C →
      bvmLocalScale θ₀ n ⁻¹' D ⊆ Metric.ball θ₀ r₀ := by
    intro D hD θ hθ
    have h1 : bvmLocalScale θ₀ n θ ∈ C := hD hθ
    rw [hCdef, Metric.mem_closedBall, dist_zero_right, bvmLocalScale, norm_smul,
      Real.norm_eq_abs, abs_of_pos hsqrt] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : Real.sqrt n * ‖θ - θ₀‖ < Real.sqrt n * r₀ :=
      lt_of_le_of_lt h1 (by rw [mul_comm]; exact hn)
    exact lt_of_mul_lt_mul_left h2 hsqrt.le
  have hdens_meas : Measurable
      (Function.uncurry fun θ (x : 𝓧) => ENNReal.ofReal (M.density θ x)) :=
    ENNReal.measurable_ofReal.comp hM_joint
  have hP : Measurable (Function.uncurry
      fun (θ : EuclideanSpace ℝ (Fin k)) (x : Fin n → 𝓧) =>
        ∏ i, ENNReal.ofReal (M.density θ (x i))) :=
    measurable_uncurry_prod_likelihood hdens_meas
  have hκ' : ∀ θ, iidKernel κ n θ
      = (Measure.pi fun _ : Fin n => μ).withDensity
          fun x => ∏ i, ENNReal.ofReal (M.density θ (x i)) :=
    fun θ => iidKernel_withDensity hdens_meas hκ n θ
  have hqpos : (0 : ℝ) < ((Real.sqrt n)⁻¹) ^ k := by positivity
  have hq : ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  filter_upwards [posterior_iid_eq_withDensity_prod_likelihood hdens_meas hκ n,
    posterior_apply_eq_div (π := π) hP hκ' (MeasurableSet.univ
      (α := EuclideanSpace ℝ (Fin k)))] with ω hωpost hωU hS
  set Z := ∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π with hZdef
  have hZ1 : Z / Z = 1 := by
    have h := hωU
    simp only [Measure.restrict_univ, measure_univ] at h
    exact h.symm
  have hZne : Z ≠ 0 := by intro h0; rw [h0] at hZ1; simp at hZ1
  have hZtop : Z ≠ ∞ := by intro h0; rw [h0] at hZ1; simp at hZ1
  have hpostB : ∀ B : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet B →
      ((iidKernel κ n)†π) ω B
        = (∫⁻ θ in B, (∏ i, ENNReal.ofReal (M.density θ (ω i))) ∂π) / Z := by
    intro B hB
    rw [hωpost, withDensity_apply _ hB]
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hZne)
  have hmap : ∀ S : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet S →
      bvmLocalPosterior κ π θ₀ n ω S
        = ((iidKernel κ n)†π) ω (bvmLocalScale θ₀ n ⁻¹' S) := by
    intro S hS'
    rw [bvmLocalPosterior, Kernel.map_apply' _ (measurable_bvmLocalScale θ₀ n) _ hS']
  ext A hA
  rw [ProbabilityTheory.cond_apply hC, hmap C hC, hmap (C ∩ A) (hC.inter hA),
    hpostB _ ((measurable_bvmLocalScale θ₀ n) hC),
    hpostB _ ((measurable_bvmLocalScale θ₀ n) (hC.inter hA)),
    lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 hC (hsub C le_rfl) ω,
    lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 (hC.inter hA)
      (hsub (C ∩ A) Set.inter_subset_left) ω,
    Set.inter_comm C A, ennreal_posterior_ratio hq ENNReal.ofReal_ne_top hZne hZtop,
    withDensity_apply _ hA, Measure.restrict_restrict hA]
  simp_rw [div_eq_mul_inv]
  exact (lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hS)).symm

-- LEAN-ONLY: measurability of the local joint density along measurable selections.
private lemma measurable_bvmJointDens_comp {α : Type*} [MeasurableSpace α]
    (hM_joint : Measurable (Function.uncurry M.density)) (hf : Measurable f) (n : ℕ)
    {a : α → EuclideanSpace ℝ (Fin k)} {b : α → Fin n → 𝓧}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x : α => bvmJointDens M f θ₀ n (a x) (b x) := by
  have hun : Measurable fun x : α => bvmLocalUnscale θ₀ n (a x) :=
    (measurable_bvmLocalUnscale θ₀ n).comp ha
  unfold bvmJointDens
  refine Measurable.mul ?_ ?_
  · refine Finset.measurable_prod Finset.univ fun i _ => ?_
    exact ENNReal.measurable_ofReal.comp
      (hM_joint.comp (hun.prodMk ((measurable_pi_apply i).comp hb)))
  · exact ENNReal.measurable_ofReal.comp (hf.comp hun)

-- LEAN-ONLY: measurability of the unnormalized Gaussian density along measurable selections.
private lemma measurable_bvmGaussDens_comp {α : Type*} [MeasurableSpace α]
    (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ)
    {a : α → EuclideanSpace ℝ (Fin k)} {b : α → Fin n → 𝓧}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x : α => bvmGaussDens J sc n (a x) (b x) := by
  have hsum : Measurable fun ω : Fin n → 𝓧 => ∑ i, sc (ω i) :=
    Finset.measurable_sum Finset.univ fun i _ => hsc.comp (measurable_pi_apply i)
  have hscore : Measurable fun ω : Fin n → 𝓧 => scoreSum sc n ω := by
    simp only [scoreSum]
    exact hsum.const_smul ((Real.sqrt (n : ℝ))⁻¹)
  have hinner : Measurable fun x : α => ⟪a x, scoreSum sc n (b x)⟫ :=
    ha.inner (hscore.comp hb)
  have hquad : Measurable fun x : α =>
      (1 / 2 : ℝ) * ⟪a x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (a x)⟫ := by
    have hcont : Continuous fun y : EuclideanSpace ℝ (Fin k) =>
        (1 / 2 : ℝ) * ⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) y⟫ := by fun_prop
    exact hcont.measurable.comp ha
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp (hinner.sub hquad))

-- LEAN-ONLY: a scalar cancellation used to strip the local-mass normalizer.
private lemma ennreal_inv_mul_mul_le (S G : ℝ≥0∞) : S⁻¹ * G * S ≤ G := by
  rcases eq_or_ne S 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne S ∞ with hT | hT
  · simp [hT]
  · rw [show S⁻¹ * G * S = S⁻¹ * S * G from by ring, ENNReal.inv_mul_cancel h0 hT, one_mul]

/-- The **pair defect** of vdV p. 143, in `t`-normalized form: the antisymmetric numerator
`s(h) t(g) − s(g) t(h)` divided by `t(g)`. Integrating it over `C × C` and normalizing by the
local mass majorizes the conditioned total-variation distance. -/
private noncomputable def bvmPairDefect (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ) (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (h g : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  (bvmJointDens M f θ₀ n h ω * bvmGaussDens J sc n g ω
      - bvmJointDens M f θ₀ n g ω * bvmGaussDens J sc n h ω) / bvmGaussDens J sc n g ω

/-- The **Step-B majorant**: the normalized double integral of the pair defect over the fixed
ball `C = B̄(0,R)`. -/
private noncomputable def bvmStepBBound (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ) (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (R : ℝ)
    (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  (bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω)⁻¹
    * ∫⁻ h in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
        ∫⁻ g in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
          bvmPairDefect M f θ₀ J sc n h g ω ∂volume ∂volume

-- LEAN-ONLY: the pointwise Step-B majorization. Where the Bayes formula holds, the local mass
-- is nondegenerate and the score sum is bounded by `K`, the conditioned total-variation
-- distance is at most a `(R, K, J)`-constant times `bvmStepBBound`.
-- LEAN-ONLY: the pair-ratio Jensen bound, post-composed with a uniform upper bound `c` on the
-- normalized second density. This is the shape consumed by Step B: the second (Gaussian)
-- normalizer is eliminated in favour of a `(R, K, J)`-constant.
private lemma tvDist_normalize_le_const_mul {α : Type*} [MeasurableSpace α]
    (base : Measure α) {s t : α → ℝ≥0∞} (hs : Measurable s) (ht : Measurable t)
    (hs0 : ∫⁻ y, s y ∂base ≠ 0) (hsT : ∫⁻ y, s y ∂base ≠ ∞)
    (ht0 : ∫⁻ y, t y ∂base ≠ 0) (htT : ∫⁻ y, t y ∂base ≠ ∞)
    (htpos : ∀ x, t x ≠ 0) (htfin : ∀ x, t x ≠ ∞)
    {c : ℝ≥0∞} (hcT : c ≠ ∞) (hc : ∀ᵐ x ∂base, t x / (∫⁻ y, t y ∂base) ≤ c) :
    Minimaxity.tvDist (base.withDensity fun x => s x / ∫⁻ y, s y ∂base)
        (base.withDensity fun x => t x / ∫⁻ y, t y ∂base)
      ≤ c * ((∫⁻ y, s y ∂base)⁻¹
          * ∫⁻ h, ∫⁻ g, (s h * t g - s g * t h) / t g ∂base ∂base) := by
  classical
  refine le_trans (tvDist_normalize_le_double_lintegral_antisymm base hs ht
    hs0 hsT ht0 htT) ?_
  set Zs := ∫⁻ y, s y ∂base with hZs
  set Zt := ∫⁻ y, t y ∂base with hZt
  have hinner : ∀ h : α, Zt⁻¹ * ∫⁻ g, (s h * t g - s g * t h) ∂base
      ≤ c * ∫⁻ g, (s h * t g - s g * t h) / t g ∂base := by
    intro h
    have hL : Zt⁻¹ * ∫⁻ g, (s h * t g - s g * t h) ∂base
        = ∫⁻ g, Zt⁻¹ * (s h * t g - s g * t h) ∂base :=
      (lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr ht0)).symm
    have hRr : c * ∫⁻ g, (s h * t g - s g * t h) / t g ∂base
        = ∫⁻ g, c * ((s h * t g - s g * t h) / t g) ∂base :=
      (lintegral_const_mul' _ _ hcT).symm
    rw [hL, hRr]
    refine lintegral_mono_ae ?_
    filter_upwards [hc] with g hcg
    have hkey : Zt⁻¹ * (s h * t g - s g * t h)
        = (t g)⁻¹ * ((t g / Zt) * (s h * t g - s g * t h)) := by
      rw [div_eq_mul_inv,
        show (t g)⁻¹ * (t g * Zt⁻¹ * (s h * t g - s g * t h))
          = (t g)⁻¹ * t g * (Zt⁻¹ * (s h * t g - s g * t h)) from by ring,
        ENNReal.inv_mul_cancel (htpos g) (htfin g), one_mul]
    rw [hkey, div_eq_mul_inv]
    calc (t g)⁻¹ * (t g / Zt * (s h * t g - s g * t h))
        ≤ (t g)⁻¹ * (c * (s h * t g - s g * t h)) :=
          mul_le_mul_right (mul_le_mul_left hcg _) _
      _ = c * ((s h * t g - s g * t h) * (t g)⁻¹) := by ring
  have hE1 : (Zs * Zt)⁻¹ * ∫⁻ h, ∫⁻ g, (s h * t g - s g * t h) ∂base ∂base
      = Zs⁻¹ * ∫⁻ h, Zt⁻¹ * ∫⁻ g, (s h * t g - s g * t h) ∂base ∂base := by
    rw [ENNReal.mul_inv (Or.inl hs0) (Or.inl hsT), mul_assoc,
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr ht0)]
  have hE2 : Zs⁻¹ * ∫⁻ h, c * ∫⁻ g, (s h * t g - s g * t h) / t g ∂base ∂base
      = c * (Zs⁻¹ * ∫⁻ h, ∫⁻ g, (s h * t g - s g * t h) / t g ∂base ∂base) := by
    rw [lintegral_const_mul' _ _ hcT]; ring
  rw [hE1, ← hE2]
  exact mul_le_mul_right (lintegral_mono hinner) _

-- LEAN-ONLY: the pointwise Step-B majorization. Where the Bayes formula holds, the local mass
-- is nondegenerate and the score sum is bounded by `K`, the conditioned total-variation
-- distance is at most a `(R, K, J)`-constant times `bvmStepBBound`.
-- The elaboration of the two `withDensity` rewrites plus the normalized Jensen bound exceeds
-- the default heartbeat budget (large `ℝ≥0∞` density terms), hence the raised limit.
set_option maxHeartbeats 1000000 in
private lemma tvDist_cond_le_bvmStepBBound
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef) {R K : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hR : 0 < R)
    -- LEAN-ONLY: the rescaled ball sits inside the absolute-continuity zone
    {n : ℕ} (hn : R < r₀ * Real.sqrt n) :
    ∀ᵐ ω ∂(iidKernel κ n ∘ₘ π),
      bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω ≠ 0 →
        bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω ≠ ∞ →
          ‖scoreSum sc n ω‖ ≤ K →
            Minimaxity.tvDist
                ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall
                  (0 : EuclideanSpace ℝ (Fin k)) R])
                ((bvmGaussian J sc n ω)[|Metric.closedBall
                  (0 : EuclideanSpace ℝ (Fin k)) R])
              ≤ ENNReal.ofReal (Real.exp
                    (2 * (R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2)))
                  / volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R)
                * bvmStepBBound M f θ₀ J sc n R ω := by
  classical
  have hC : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) :=
    measurableSet_closedBall
  have hV0 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) ≠ 0 :=
    (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 hR)
      (measure_mono Metric.ball_subset_closedBall)).ne'
  have hcT : ENNReal.ofReal (Real.exp
        (2 * (R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2)))
        / volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) ≠ ∞ :=
    ENNReal.div_ne_top ENNReal.ofReal_ne_top hV0
  filter_upwards [cond_bvmLocalPosterior_eq_withDensity_ae hκ hM_joint hπ hR hn]
    with ω hωpost hS hSfin hK
  have hun : Measurable fun hh : EuclideanSpace ℝ (Fin k) => bvmLocalUnscale θ₀ n hh :=
    measurable_bvmLocalUnscale θ₀ n
  have hsmeas : Measurable fun h : EuclideanSpace ℝ (Fin k) => bvmJointDens M f θ₀ n h ω := by
    unfold bvmJointDens
    refine Measurable.mul (Finset.measurable_prod Finset.univ fun i _ => ?_) ?_
    · exact ENNReal.measurable_ofReal.comp (hM_joint.comp (hun.prodMk measurable_const))
    · exact ENNReal.measurable_ofReal.comp (hπ.measurable.comp hun)
  have htmeas : Measurable fun h : EuclideanSpace ℝ (Fin k) => bvmGaussDens J sc n h ω :=
    measurable_bvmGaussDens J sc n ω
  have hT0 : (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
      bvmGaussDens J sc n y ω) ≠ 0 := (lintegral_bvmGaussDens_pos J sc hR n ω).ne'
  have hTT : (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
      bvmGaussDens J sc n y ω) ≠ ∞ := lintegral_bvmGaussDens_ne_top J sc hR.le n ω
  have htpos : ∀ x : EuclideanSpace ℝ (Fin k), bvmGaussDens J sc n x ω ≠ 0 := by
    intro x
    simp only [bvmGaussDens, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  have htfin : ∀ x : EuclideanSpace ℝ (Fin k), bvmGaussDens J sc n x ω ≠ ∞ := by
    intro x
    simp only [bvmGaussDens]
    exact ENNReal.ofReal_ne_top
  have hc : ∀ᵐ x ∂(volume.restrict
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R)),
      bvmGaussDens J sc n x ω
          / (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
              bvmGaussDens J sc n y ω)
        ≤ ENNReal.ofReal (Real.exp
              (2 * (R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2)))
            / volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) := by
    refine ae_restrict_of_forall_mem hC fun g hg => ?_
    rw [Metric.mem_closedBall, dist_zero_right] at hg
    exact bvmGaussDens_div_lintegral_le J sc hR hK hg
  rw [hωpost hS, cond_bvmGaussian_eq_withDensity hJ_pd n ω hC]
  exact tvDist_normalize_le_const_mul
    (volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R))
    (s := fun h => bvmJointDens M f θ₀ n h ω) (t := fun h => bvmGaussDens J sc n h ω)
    hsmeas htmeas hS hSfin hT0 hTT htpos htfin hcT hc

-- LEAN-ONLY: joint measurability of the pair defect in `(ω, h, g)`.
private lemma measurable_bvmPairDefect
    (hM_joint : Measurable (Function.uncurry M.density)) (hf : Measurable f)
    (J : Matrix (Fin k) (Fin k) ℝ) {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc)
    (n : ℕ) :
    Measurable fun q : ((Fin n → 𝓧) × EuclideanSpace ℝ (Fin k))
        × EuclideanSpace ℝ (Fin k) => bvmPairDefect M f θ₀ J sc n q.1.2 q.2 q.1.1 := by
  have hsh := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun q : ((Fin n → 𝓧) × EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k) => q.1.2)
    (b := fun q => q.1.1) measurable_fst.snd measurable_fst.fst
  have hsg := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun q : ((Fin n → 𝓧) × EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k) => q.2)
    (b := fun q => q.1.1) measurable_snd measurable_fst.fst
  have hth := measurable_bvmGaussDens_comp J hsc n
    (a := fun q : ((Fin n → 𝓧) × EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k) => q.1.2)
    (b := fun q => q.1.1) measurable_fst.snd measurable_fst.fst
  have htg := measurable_bvmGaussDens_comp J hsc n
    (a := fun q : ((Fin n → 𝓧) × EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k) => q.2)
    (b := fun q => q.1.1) measurable_snd measurable_fst.fst
  unfold bvmPairDefect
  exact ((hsh.mul htg).sub (hsg.mul hth)).div htg

-- LEAN-ONLY: measurability of the Step-B majorant as a statistic.
private lemma measurable_bvmStepBBound
    (hM_joint : Measurable (Function.uncurry M.density)) (hf : Measurable f)
    (J : Matrix (Fin k) (Fin k) ℝ) {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc)
    (n : ℕ) (R : ℝ) :
    Measurable (bvmStepBBound M f θ₀ J sc n R) := by
  have h1 := (measurable_bvmPairDefect (M := M) (θ₀ := θ₀) hM_joint hf J hsc n)
  have h2 : Measurable fun p : (Fin n → 𝓧) × EuclideanSpace ℝ (Fin k) =>
      ∫⁻ g in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
        bvmPairDefect M f θ₀ J sc n p.2 g p.1 ∂volume :=
    h1.lintegral_prod_right'
      (ν := volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R))
  have h3 : Measurable fun ω : Fin n → 𝓧 =>
      ∫⁻ h in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
        ∫⁻ g in Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R,
          bvmPairDefect M f θ₀ J sc n h g ω ∂volume ∂volume :=
    h2.lintegral_prod_right'
      (ν := volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R))
  unfold bvmStepBBound
  exact ((measurable_bvmNumer (θ₀ := θ₀) hM_joint hf n measurableSet_closedBall).inv).mul h3

-- LEAN-ONLY: the localized prior mixture, written as a density against the dominating product
-- measure. The Jacobian and the prior small-ball mass are the two scalars; the density itself
-- is `bvmNumer` on the local ball.
private lemma lintegral_bvmMixture_eq
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {u : ℝ}
    -- LEAN-ONLY: the rescaled ball sits inside the absolute-continuity zone
    {n : ℕ} (hn1 : 1 ≤ n) (hn : u < r₀ * Real.sqrt n)
    {F : (Fin n → 𝓧) → ℝ≥0∞}
    -- LEAN-ONLY: measurable integrand (regularity)
    (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(bvmMixture κ π θ₀ u n)
      = (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ * ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k)
          * ∫⁻ ω, F ω * bvmNumer M f θ₀ n (Metric.ball 0 u) ω
              ∂(Measure.pi fun _ : Fin n => μ) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hdens_meas : Measurable
      (Function.uncurry fun θ (x : 𝓧) => ENNReal.ofReal (M.density θ x)) :=
    ENNReal.measurable_ofReal.comp hM_joint
  have hκ' : ∀ θ, iidKernel κ n θ
      = (Measure.pi fun _ : Fin n => μ).withDensity
          fun x => ∏ i, ENNReal.ofReal (M.density θ (x i)) :=
    fun θ => iidKernel_withDensity hdens_meas hκ n θ
  have hlik : Measurable fun p : EuclideanSpace ℝ (Fin k) × (Fin n → 𝓧) =>
      ∏ i, ENNReal.ofReal (M.density p.1 (p.2 i)) := by
    refine Finset.measurable_prod Finset.univ fun i _ => ?_
    exact ENNReal.measurable_ofReal.comp
      (hM_joint.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hlikθ : ∀ θ : EuclideanSpace ℝ (Fin k),
      Measurable fun x : Fin n → 𝓧 => ∏ i, ENNReal.ofReal (M.density θ (x i)) := by
    intro θ
    refine Finset.measurable_prod Finset.univ fun i _ => ?_
    exact ENNReal.measurable_ofReal.comp
      (hM_joint.comp (measurable_const.prodMk (measurable_pi_apply i)))
  have hball : bvmLocalScale θ₀ n ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u)
      = Metric.ball θ₀ (u / Real.sqrt n) := by
    ext θ
    simp only [Set.mem_preimage, Metric.mem_ball, bvmLocalScale, sub_zero,
      norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt, dist_eq_norm]
    rw [lt_div_iff₀ hsqrt, mul_comm (Real.sqrt (n : ℝ)) ‖θ - θ₀‖]
  have hsub : bvmLocalScale θ₀ n ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u)
      ⊆ Metric.ball θ₀ r₀ := by
    rw [hball]
    refine Metric.ball_subset_ball ?_
    rw [div_le_iff₀ hsqrt]
    exact hn.le
  -- Step 1: unfold the mixture.
  have step1 : ∫⁻ ω, F ω ∂(bvmMixture κ π θ₀ u n)
      = (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹
          * ∫⁻ θ in Metric.ball θ₀ (u / Real.sqrt n),
              ∫⁻ ω, F ω ∂(iidKernel κ n θ) ∂π := by
    unfold bvmMixture
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable,
      ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
  -- Step 2: the per-parameter integral against the dominating measure.
  have step2 : ∀ θ : EuclideanSpace ℝ (Fin k), ∫⁻ ω, F ω ∂(iidKernel κ n θ)
      = ∫⁻ ω, (∏ i, ENNReal.ofReal (M.density θ (ω i))) * F ω
          ∂(Measure.pi fun _ : Fin n => μ) := by
    intro θ
    rw [hκ' θ, lintegral_withDensity_eq_lintegral_mul _ (hlikθ θ) hF]
    rfl
  -- Step 3: Tonelli.
  have hjoint : Measurable (Function.uncurry
      fun (θ : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) =>
        (∏ i, ENNReal.ofReal (M.density θ (ω i))) * F ω) := by
    unfold Function.uncurry
    exact hlik.mul (hF.comp measurable_snd)
  have step3 : ∫⁻ θ in Metric.ball θ₀ (u / Real.sqrt n),
        ∫⁻ ω, (∏ i, ENNReal.ofReal (M.density θ (ω i))) * F ω
          ∂(Measure.pi fun _ : Fin n => μ) ∂π
      = ∫⁻ ω, ∫⁻ θ in Metric.ball θ₀ (u / Real.sqrt n),
          (∏ i, ENNReal.ofReal (M.density θ (ω i))) * F ω ∂π
          ∂(Measure.pi fun _ : Fin n => μ) :=
    lintegral_lintegral_swap hjoint.aemeasurable
  -- Step 4: the inner prior integral is the Jacobian times `bvmNumer`.
  have step4 : ∀ ω : Fin n → 𝓧,
      ∫⁻ θ in Metric.ball θ₀ (u / Real.sqrt n),
          (∏ i, ENNReal.ofReal (M.density θ (ω i))) * F ω ∂π
        = ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k)
            * (F ω * bvmNumer M f θ₀ n (Metric.ball 0 u) ω) := by
    intro ω
    have hae : AEMeasurable (fun θ : EuclideanSpace ℝ (Fin k) =>
        ∏ i, ENNReal.ofReal (M.density θ (ω i)))
        (π.restrict (Metric.ball θ₀ (u / Real.sqrt n))) :=
      (hlik.comp (measurable_id.prodMk measurable_const)).aemeasurable
    rw [lintegral_mul_const'' _ hae, ← hball,
      lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 measurableSet_ball hsub ω]
    ring
  rw [step1]
  simp_rw [step2]
  rw [step3]
  simp_rw [step4]
  rw [lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top (r := ((Real.sqrt (n : ℝ))⁻¹) ^ k)),
    ← mul_assoc]

-- LEAN-ONLY: on the common-support rectangle the `ℝ≥0∞` pair ratio is the exponential of
-- `bvmLogRatio`. (Off that rectangle they differ: `logLikelihood` is a sum of logarithms of
-- density *ratios*, which is junk where a density vanishes.)
private lemma bvmPairRatio_eq_exp_bvmLogRatio {g h : EuclideanSpace ℝ (Fin k)} {n : ℕ}
    {ω : Fin n → 𝓧}
    (hfg : 0 < f (bvmLocalUnscale θ₀ n g)) (hfh : 0 < f (bvmLocalUnscale θ₀ n h))
    (h0 : ∀ i, 0 < M.density θ₀ (ω i))
    (hgpos : ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n g) (ω i))
    (hhpos : ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n h) (ω i)) :
    bvmJointDens M f θ₀ n g ω * bvmGaussDens J sc n h ω
        / (bvmJointDens M f θ₀ n h ω * bvmGaussDens J sc n g ω)
      = ENNReal.ofReal (Real.exp (bvmLogRatio M f θ₀ J sc n g h ω)) := by
  classical
  set qg : ℝ := ⟪g, scoreSum sc n ω⟫
      - (1 / 2 : ℝ) * ⟪g, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) g))⟫ with hqg
  set qh : ℝ := ⟪h, scoreSum sc n ω⟫
      - (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ with hqh
  set Pg : ℝ := ∏ i, M.density (bvmLocalUnscale θ₀ n g) (ω i) with hPgd
  set Ph : ℝ := ∏ i, M.density (bvmLocalUnscale θ₀ n h) (ω i) with hPhd
  set P0 : ℝ := ∏ i, M.density θ₀ (ω i) with hP0d
  have hPg : 0 < Pg := Finset.prod_pos fun i _ => hgpos i
  have hPh : 0 < Ph := Finset.prod_pos fun i _ => hhpos i
  have hP0 : 0 < P0 := Finset.prod_pos fun i _ => h0 i
  have hJg : bvmJointDens M f θ₀ n g ω
      = ENNReal.ofReal (Pg * f (bvmLocalUnscale θ₀ n g)) := by
    rw [ENNReal.ofReal_mul hPg.le, hPgd,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => M.density_nonneg _ _)]
    rfl
  have hJh : bvmJointDens M f θ₀ n h ω
      = ENNReal.ofReal (Ph * f (bvmLocalUnscale θ₀ n h)) := by
    rw [ENNReal.ofReal_mul hPh.le, hPhd,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => M.density_nonneg _ _)]
    rfl
  have hGg : bvmGaussDens J sc n g ω = ENNReal.ofReal (Real.exp qg) := by rw [hqg]; rfl
  have hGh : bvmGaussDens J sc n h ω = ENNReal.ofReal (Real.exp qh) := by rw [hqh]; rfl
  have hnum : 0 < Pg * f (bvmLocalUnscale θ₀ n g) * Real.exp qh :=
    mul_pos (mul_pos hPg hfg) (Real.exp_pos _)
  have hden : 0 < Ph * f (bvmLocalUnscale θ₀ n h) * Real.exp qg :=
    mul_pos (mul_pos hPh hfh) (Real.exp_pos _)
  -- the log-likelihood in terms of the product densities
  have hL : ∀ x : EuclideanSpace ℝ (Fin k),
      (∀ i, 0 < M.density (bvmLocalUnscale θ₀ n x) (ω i)) →
      logLikelihood M θ₀ x n ω
        = Real.log (∏ i, M.density (bvmLocalUnscale θ₀ n x) (ω i)) - Real.log P0 := by
    intro x hx
    have hsplit : ∀ i : Fin n,
        Real.log (M.density (bvmLocalUnscale θ₀ n x) (ω i) / M.density θ₀ (ω i))
          = Real.log (M.density (bvmLocalUnscale θ₀ n x) (ω i)) - Real.log (M.density θ₀ (ω i)) :=
      fun i => Real.log_div (hx i).ne' (h0 i).ne'
    rw [Real.log_prod (fun i _ => (hx i).ne'), hP0d,
      Real.log_prod (fun i _ => (h0 i).ne')]
    change ∑ i, Real.log (M.density (θ₀ + (Real.sqrt n)⁻¹ • x) (ω i)
      / M.density θ₀ (ω i)) = _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hsplit i
  have hinnersub : ⟪g - h, scoreSum sc n ω⟫
      = ⟪g, scoreSum sc n ω⟫ - ⟪h, scoreSum sc n ω⟫ := inner_sub_left (𝕜 := ℝ) _ _ _
  have hratio : (Pg * f (bvmLocalUnscale θ₀ n g) * Real.exp qh)
      / (Ph * f (bvmLocalUnscale θ₀ n h) * Real.exp qg)
      = Real.exp (bvmLogRatio M f θ₀ J sc n g h ω) := by
    rw [← Real.exp_log hnum, ← Real.exp_log hden, ← Real.exp_sub]
    congr 1
    rw [Real.log_mul (mul_pos hPg hfg).ne' (Real.exp_ne_zero _), Real.log_mul hPg.ne' hfg.ne',
      Real.log_mul (mul_pos hPh hfh).ne' (Real.exp_ne_zero _), Real.log_mul hPh.ne' hfh.ne',
      Real.log_exp, Real.log_exp, bvmLogRatio, hL g hgpos, hL h hhpos, hinnersub, ← hPgd, ← hPhd]
    simp only [hqg, hqh]
    ring
  rw [hJg, hJh, hGg, hGh, ← ENNReal.ofReal_mul (mul_pos hPg hfg).le,
    ← ENNReal.ofReal_mul (mul_pos hPh hfh).le, ← ENNReal.ofReal_div_of_pos hden, hratio]

-- LEAN-ONLY: the algebraic identity turning the pair defect into `s(h) · (1 − ρ)`.
private lemma ennreal_defect_eq {A B C D : ℝ≥0∞} (hA : A ≠ ∞) (hD0 : D ≠ 0) (hDT : D ≠ ∞) :
    (A * D - C * B) / D = A * (1 - C * B / (A * D)) := by
  rcases eq_or_ne A 0 with hA0 | hA0
  · simp [hA0]
  · have hcancel : A * (C * B / (A * D)) = C * B / D := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hA0) (Or.inl hA),
        show A * (C * B * (A⁻¹ * D⁻¹)) = A * A⁻¹ * (C * B * D⁻¹) from by ring,
        ENNReal.mul_inv_cancel hA0 hA, one_mul]
    have hAD : A * D / D = A := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hD0 hDT, mul_one]
    rw [ENNReal.mul_sub (fun _ _ => hA), mul_one, hcancel,
      ENNReal.sub_div (fun _ _ => hD0), hAD]

-- LEAN-ONLY: the local joint density is finite.
private lemma bvmJointDens_ne_top (n : ℕ) (h : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) :
    bvmJointDens M f θ₀ n h ω ≠ ∞ := by
  have hprod : (∏ i, ENNReal.ofReal (M.density (bvmLocalUnscale θ₀ n h) (ω i)))
      = ENNReal.ofReal (∏ i, M.density (bvmLocalUnscale θ₀ n h) (ω i)) :=
    (ENNReal.ofReal_prod_of_nonneg (fun i _ => M.density_nonneg _ _)).symm
  rw [bvmJointDens, hprod]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

private lemma bvmGaussDens_ne_zero (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (h : EuclideanSpace ℝ (Fin k))
    (ω : Fin n → 𝓧) : bvmGaussDens J sc n h ω ≠ 0 := by
  simp only [bvmGaussDens, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Real.exp_pos _

private lemma bvmGaussDens_ne_top' (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (h : EuclideanSpace ℝ (Fin k))
    (ω : Fin n → 𝓧) : bvmGaussDens J sc n h ω ≠ ∞ := by
  simp only [bvmGaussDens]
  exact ENNReal.ofReal_ne_top

-- LEAN-ONLY: the pair defect as local joint density times the truncated pair-ratio defect.
private lemma bvmPairDefect_eq (n : ℕ) (h g : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) :
    bvmPairDefect M f θ₀ J sc n h g ω
      = bvmJointDens M f θ₀ n h ω
          * (1 - bvmJointDens M f θ₀ n g ω * bvmGaussDens J sc n h ω
              / (bvmJointDens M f θ₀ n h ω * bvmGaussDens J sc n g ω)) :=
  ennreal_defect_eq (bvmJointDens_ne_top n h ω) (bvmGaussDens_ne_zero J sc n g ω)
    (bvmGaussDens_ne_top' J sc n g ω)

private lemma bvmPairDefect_le (n : ℕ) (h g : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) :
    bvmPairDefect M f θ₀ J sc n h g ω ≤ bvmJointDens M f θ₀ n h ω := by
  rw [bvmPairDefect_eq]
  exact mul_le_of_le_one_right' (by simp)

-- LEAN-ONLY: integrating the local joint density against the dominating measure turns it into
-- the prior density times the sampling law at `θ₀ + h/√n`.
private lemma lintegral_bvmJointDens_mul
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    {n : ℕ} (h : EuclideanSpace ℝ (Fin k)) {X : (Fin n → 𝓧) → ℝ≥0∞}
    -- LEAN-ONLY: measurable integrand (regularity)
    (hX : Measurable X) :
    ∫⁻ ω, bvmJointDens M f θ₀ n h ω * X ω ∂(Measure.pi fun _ : Fin n => μ)
      = ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h))
          * ∫⁻ ω, X ω ∂(productMeasure M μ (bvmLocalUnscale θ₀ n h) n) := by
  classical
  have hdens_meas : Measurable
      (Function.uncurry fun θ (x : 𝓧) => ENNReal.ofReal (M.density θ x)) :=
    ENNReal.measurable_ofReal.comp hM_joint
  have hlikθ : Measurable fun x : Fin n → 𝓧 =>
      ∏ i, ENNReal.ofReal (M.density (bvmLocalUnscale θ₀ n h) (x i)) := by
    refine Finset.measurable_prod Finset.univ fun i _ => ?_
    exact ENNReal.measurable_ofReal.comp
      (hM_joint.comp (measurable_const.prodMk (measurable_pi_apply i)))
  have hPθ : productMeasure M μ (bvmLocalUnscale θ₀ n h) n
      = (Measure.pi fun _ : Fin n => μ).withDensity
          fun x => ∏ i, ENNReal.ofReal (M.density (bvmLocalUnscale θ₀ n h) (x i)) := by
    rw [productMeasure_eq_iidKernel_apply hκ (bvmLocalUnscale θ₀ n h) n]
    exact iidKernel_withDensity hdens_meas hκ n _
  rw [hPθ, lintegral_withDensity_eq_lintegral_mul _ hlikθ hX,
    ← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top
      (r := f (bvmLocalUnscale θ₀ n h)))]
  refine lintegral_congr fun ω => ?_
  simp only [bvmJointDens, Pi.mul_apply]
  ring

private lemma lintegral_bvmPairDefect_le
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    {n : ℕ} (h g : EuclideanSpace ℝ (Fin k)) :
    ∫⁻ ω, bvmPairDefect M f θ₀ J sc n h g ω ∂(Measure.pi fun _ : Fin n => μ)
      ≤ ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h)) := by
  haveI : IsProbabilityMeasure (productMeasure M μ (bvmLocalUnscale θ₀ n h) n) :=
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF _ n
  calc ∫⁻ ω, bvmPairDefect M f θ₀ J sc n h g ω ∂(Measure.pi fun _ : Fin n => μ)
      ≤ ∫⁻ ω, bvmJointDens M f θ₀ n h ω ∂(Measure.pi fun _ : Fin n => μ) :=
        lintegral_mono fun ω => bvmPairDefect_le n h g ω
    _ = ∫⁻ ω, bvmJointDens M f θ₀ n h ω * 1 ∂(Measure.pi fun _ : Fin n => μ) := by
        simp
    _ = ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h))
          * ∫⁻ _, (1 : ℝ≥0∞) ∂(productMeasure M μ (bvmLocalUnscale θ₀ n h) n) :=
        lintegral_bvmJointDens_mul hκ hM_joint h measurable_const
    _ = ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h)) := by simp

-- LEAN-ONLY: Markov-type split for a `[0,1]`-valued integrand.
private lemma lintegral_le_add_measure_gt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} (hY : Measurable Y) (hY1 : ∀ ω, Y ω ≤ 1)
    (a : ℝ≥0∞) : ∫⁻ ω, Y ω ∂P ≤ a + P {ω | a < Y ω} := by
  have hS : MeasurableSet {ω | a < Y ω} := measurableSet_lt measurable_const hY
  rw [← lintegral_add_compl Y hS]
  have h1 : ∫⁻ ω in {ω | a < Y ω}, Y ω ∂P ≤ P {ω | a < Y ω} := by
    calc ∫⁻ ω in {ω | a < Y ω}, Y ω ∂P ≤ ∫⁻ _ in {ω | a < Y ω}, (1 : ℝ≥0∞) ∂P :=
          lintegral_mono fun ω => hY1 ω
      _ = P {ω | a < Y ω} := setLIntegral_one _
  have h2 : ∫⁻ ω in {ω | a < Y ω}ᶜ, Y ω ∂P ≤ a := by
    calc ∫⁻ ω in {ω | a < Y ω}ᶜ, Y ω ∂P ≤ ∫⁻ _ in {ω | a < Y ω}ᶜ, a ∂P :=
          setLIntegral_mono_ae measurable_const.aemeasurable
            (Filter.Eventually.of_forall fun ω hω => by
              simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
              exact hω)
      _ = a * P {ω | a < Y ω}ᶜ := setLIntegral_const _ _
      _ ≤ a := by
          calc a * P {ω | a < Y ω}ᶜ ≤ a * 1 := mul_le_mul_right prob_le_one _
            _ = a := mul_one a
  calc ∫⁻ ω in {ω | a < Y ω}, Y ω ∂P + ∫⁻ ω in {ω | a < Y ω}ᶜ, Y ω ∂P
      ≤ P {ω | a < Y ω} + a := add_le_add h1 h2
    _ = a + P {ω | a < Y ω} := add_comm _ _

-- LEAN-ONLY: measurability of the common-support rectangle's complement.
private lemma measurableSet_bvmBad (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    MeasurableSet {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ (ω i)} := by
  have heq : {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ (ω i)}
      = ⋃ i : Fin n, {ω : Fin n → 𝓧 | M.density θ (ω i) ≤ 0} := by
    ext ω; simp [not_forall, not_lt]
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_le ((M.density_meas θ).comp (measurable_pi_apply i)) measurable_const

-- LEAN-ONLY: the sampling law at `θ` charges no sample where its own density vanishes.
private lemma productMeasure_bvmBad_eq_zero
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    productMeasure M μ θ n {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ (ω i)} = 0 := by
  classical
  have hdens_meas : Measurable
      (Function.uncurry fun θ' (x : 𝓧) => ENNReal.ofReal (M.density θ' x)) :=
    ENNReal.measurable_ofReal.comp hM_joint
  have hlikθ : Measurable fun x : Fin n → 𝓧 =>
      ∏ i, ENNReal.ofReal (M.density θ (x i)) :=
    Finset.measurable_prod Finset.univ fun i _ =>
      ENNReal.measurable_ofReal.comp ((M.density_meas θ).comp (measurable_pi_apply i))
  have hS := measurableSet_bvmBad (M := M) θ n
  have hPθ : productMeasure M μ θ n = (Measure.pi fun _ : Fin n => μ).withDensity
      fun x => ∏ i, ENNReal.ofReal (M.density θ (x i)) := by
    rw [productMeasure_eq_iidKernel_apply hκ θ n]
    exact iidKernel_withDensity hdens_meas hκ n θ
  rw [hPθ, withDensity_apply _ hS]
  refine setLIntegral_eq_zero hS fun ω hω => ?_
  simp only [Set.mem_setOf_eq, not_forall, not_lt] at hω
  obtain ⟨i, hi⟩ := hω
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ENNReal.ofReal_eq_zero.mpr hi)

-- LEAN-ONLY: measurability of the log pair ratio as a statistic.
private lemma measurable_bvmLogRatio (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc) (n : ℕ)
    (g h : EuclideanSpace ℝ (Fin k)) :
    Measurable fun ω : Fin n → 𝓧 => bvmLogRatio M f θ₀ J sc n g h ω := by
  have hsum : Measurable fun ω : Fin n → 𝓧 => ∑ i, sc (ω i) :=
    Finset.measurable_sum Finset.univ fun i _ => hsc.comp (measurable_pi_apply i)
  have hscore : Measurable fun ω : Fin n → 𝓧 => scoreSum sc n ω := by
    simp only [scoreSum]
    exact hsum.const_smul ((Real.sqrt (n : ℝ))⁻¹)
  unfold bvmLogRatio
  refine (((AsymptoticStatistics.AsymptoticRepresentation.logLikelihood_measurable
    M θ₀ g n).sub (AsymptoticStatistics.AsymptoticRepresentation.logLikelihood_measurable
    M θ₀ h n)).add measurable_const).sub ?_
  exact ((measurable_const.inner hscore).sub measurable_const).add measurable_const

-- LEAN-ONLY: measurability of the `ℝ≥0∞` pair ratio as a statistic.
private lemma measurable_bvmPairRatio
    (hM_joint : Measurable (Function.uncurry M.density)) (hf : Measurable f)
    (J : Matrix (Fin k) (Fin k) ℝ) {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc)
    (n : ℕ) (g h : EuclideanSpace ℝ (Fin k)) :
    Measurable fun ω : Fin n → 𝓧 =>
      bvmJointDens M f θ₀ n g ω * bvmGaussDens J sc n h ω
        / (bvmJointDens M f θ₀ n h ω * bvmGaussDens J sc n g ω) := by
  have hsg := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun _ : Fin n → 𝓧 => g) (b := fun ω => ω) measurable_const measurable_id
  have hsh := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun _ : Fin n → 𝓧 => h) (b := fun ω => ω) measurable_const measurable_id
  have htg := measurable_bvmGaussDens_comp J hsc n
    (a := fun _ : Fin n → 𝓧 => g) (b := fun ω => ω) measurable_const measurable_id
  have hth := measurable_bvmGaussDens_comp J hsc n
    (a := fun _ : Fin n → 𝓧 => h) (b := fun ω => ω) measurable_const measurable_id
  exact (hsg.mul hth).div (hsh.mul htg)

/-- **Fixed-pair vanishing of the pair defect** (vdV p. 143): for fixed `g, h` the
`μⁿ`-integral of the pair defect tends to zero. This combines `bvmLogRatio_tendsto` with
mutual contiguity of the local alternatives (to move the exceptional sets, including the
non-common-support rectangle, from `P^n_{θ₀}` to `P^n_{θ₀+h/√n}`). -/
private lemma lintegral_bvmPairDefect_tendsto
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    (g h : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n => ∫⁻ ω, bvmPairDefect M f θ₀ J sc n h g ω
        ∂(Measure.pi fun _ : Fin n => μ)) atTop (𝓝 0) := by
  classical
  haveI hProb : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) := fun θ n =>
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF θ n
  set ρ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ≥0∞ := fun n ω =>
    bvmJointDens M f θ₀ n g ω * bvmGaussDens J sc n h ω
      / (bvmJointDens M f θ₀ n h ω * bvmGaussDens J sc n g ω) with hρdef
  have hρmeas : ∀ n, Measurable (ρ n) := fun n =>
    measurable_bvmPairRatio (M := M) (θ₀ := θ₀) hM_joint hπ.measurable J hsc n g h
  have hYmeas : ∀ n, Measurable fun ω : Fin n → 𝓧 => 1 - ρ n ω := fun n =>
    measurable_const.sub (hρmeas n)
  -- the pair defect integral factorizes
  have hident : ∀ n : ℕ, ∫⁻ ω, bvmPairDefect M f θ₀ J sc n h g ω
        ∂(Measure.pi fun _ : Fin n => μ)
      = ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h))
          * ∫⁻ ω, (1 - ρ n ω) ∂(productMeasure M μ (bvmLocalUnscale θ₀ n h) n) := by
    intro n
    rw [← lintegral_bvmJointDens_mul hκ hM_joint h (hYmeas n)]
    exact lintegral_congr fun ω => bvmPairDefect_eq n h g ω
  -- the deterministic prefactor converges
  have hunsc : Tendsto (fun n : ℕ => bvmLocalUnscale θ₀ n h) atTop (𝓝 θ₀) := by
    have hsq : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hsm : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • h) atTop (𝓝 ((0 : ℝ) • h)) :=
      hsq.smul_const h
    have := tendsto_const_nhds (x := θ₀) (f := (atTop : Filter ℕ)) |>.add hsm
    simpa [bvmLocalUnscale] using this
  have hfpre : Tendsto (fun n : ℕ => ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h))) atTop
      (𝓝 (ENNReal.ofReal (f θ₀))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hπ.continuousAt.tendsto.comp hunsc)
  -- the main convergence
  have hmain : Tendsto (fun n : ℕ =>
      ∫⁻ ω, (1 - ρ n ω) ∂(productMeasure M μ (bvmLocalUnscale θ₀ n h) n)) atTop (𝓝 0) := by
    have hcontig : ∀ x : EuclideanSpace ℝ (Fin k),
        AsymptoticStatistics.Contiguity.MutuallyContiguous (ι := ℕ)
          (Ω := fun n => Fin n → 𝓧) atTop (fun n => productMeasure M μ θ₀ n)
          (fun n => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • x) n) :=
      fun x => mutuallyContiguous_local_alternative hPDF hsc hDQM hJ_pd hJ x
    -- the three exceptional rectangles vanish under `P^n_{θ₀+h/√n}`
    have hbad : ∀ x : EuclideanSpace ℝ (Fin k),
        Tendsto (fun n : ℕ => productMeasure M μ (bvmLocalUnscale θ₀ n h) n
          {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n x) (ω i)})
          atTop (𝓝 0) := by
      intro x
      refine (hcontig h).1 _ (fun n => measurableSet_bvmBad (M := M) _ n) ?_
      refine (hcontig x).2 _ (fun n => measurableSet_bvmBad (M := M) _ n) ?_
      simpa using! tendsto_const_nhds (x := (0 : ℝ≥0∞)) (f := (atTop : Filter ℕ))
        |>.congr fun n => (productMeasure_bvmBad_eq_zero hκ hM_joint
          (bvmLocalUnscale θ₀ n x) n).symm
    have hbad0 : Tendsto (fun n : ℕ => productMeasure M μ (bvmLocalUnscale θ₀ n h) n
        {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ₀ (ω i)}) atTop (𝓝 0) := by
      refine (hcontig h).1 _ (fun n => measurableSet_bvmBad (M := M) _ n) ?_
      simpa using tendsto_const_nhds (x := (0 : ℝ≥0∞)) (f := (atTop : Filter ℕ))
        |>.congr fun n => (productMeasure_bvmBad_eq_zero hκ hM_joint θ₀ n).symm
    -- the prior density is positive along both shrinking sequences
    have hfpos : ∀ x : EuclideanSpace ℝ (Fin k),
        ∀ᶠ n : ℕ in atTop, 0 < f (bvmLocalUnscale θ₀ n x) := by
      intro x
      have hx : Tendsto (fun n : ℕ => bvmLocalUnscale θ₀ n x) atTop (𝓝 θ₀) := by
        have hsq : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        have hsm : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • x) atTop (𝓝 ((0 : ℝ) • x)) :=
          hsq.smul_const x
        have := tendsto_const_nhds (x := θ₀) (f := (atTop : Filter ℕ)) |>.add hsm
        simpa [bvmLocalUnscale] using this
      exact (hπ.continuousAt.tendsto.comp hx).eventually
        (eventually_gt_nhds hπ.pos)
    -- the ε-level bound
    have hlim : ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∀ᶠ n : ℕ in atTop,
        ∫⁻ ω, (1 - ρ n ω) ∂(productMeasure M μ (bvmLocalUnscale θ₀ n h) n)
          ≤ ENNReal.ofReal (2 * ε₀) := by
      intro ε₀ hε₀ hε₀1
      have h1ε : (0 : ℝ) < 1 - ε₀ := by linarith
      set c : ℝ := -Real.log (1 - ε₀) with hcdef
      have hcpos : 0 < c := by
        rw [hcdef, neg_pos]
        exact Real.log_neg h1ε (by linarith)
      have hlr : Tendsto (fun n : ℕ => productMeasure M μ (bvmLocalUnscale θ₀ n h) n
          {ω : Fin n → 𝓧 | c ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}) atTop (𝓝 0) := by
        refine (hcontig h).1 _ (fun n => measurableSet_le measurable_const
          (measurable_bvmLogRatio (M := M) (θ₀ := θ₀) (f := f) J hsc n g h).abs) ?_
        have hreal := bvmLogRatio_tendsto (M := M) (f := f) (π := π) (r₀ := r₀)
          hPDF hsc hDQM hJ hπ g h c hcpos
        have hcong : ∀ n : ℕ, ENNReal.ofReal ((productMeasure M μ θ₀ n).real
            {ω : Fin n → 𝓧 | c ≤ |bvmLogRatio M f θ₀ J sc n g h ω|})
            = productMeasure M μ θ₀ n
                {ω : Fin n → 𝓧 | c ≤ |bvmLogRatio M f θ₀ J sc n g h ω|} := fun n => by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        have h2 := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
        rw [ENNReal.ofReal_zero] at h2
        exact Filter.Tendsto.congr (fun n => by
          simp only [Function.comp_apply]; exact hcong n) h2
      have hsum : Tendsto (fun n : ℕ =>
          productMeasure M μ (bvmLocalUnscale θ₀ n h) n
              {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ₀ (ω i)}
            + (productMeasure M μ (bvmLocalUnscale θ₀ n h) n
                {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n g) (ω i)}
              + (productMeasure M μ (bvmLocalUnscale θ₀ n h) n
                  {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n h) (ω i)}
                + productMeasure M μ (bvmLocalUnscale θ₀ n h) n
                    {ω : Fin n → 𝓧 | c ≤ |bvmLogRatio M f θ₀ J sc n g h ω|})))
          atTop (𝓝 0) := by
        simpa using hbad0.add ((hbad g).add ((hbad h).add hlr))
      have hev := (ENNReal.tendsto_nhds_zero.mp hsum) (ENNReal.ofReal ε₀)
        (by simpa using hε₀)
      filter_upwards [hev, hfpos g, hfpos h] with n hn hfg hfh
      have hincl : {ω : Fin n → 𝓧 | ENNReal.ofReal ε₀ < 1 - ρ n ω}
          ⊆ {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ₀ (ω i)}
            ∪ ({ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n g) (ω i)}
              ∪ ({ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n h) (ω i)}
                ∪ {ω : Fin n → 𝓧 | c ≤ |bvmLogRatio M f θ₀ J sc n g h ω|})) := by
        intro ω hω
        by_contra hcon
        simp only [Set.mem_union, not_or] at hcon
        obtain ⟨hc0, hcg, hch, hclr⟩ :
            ω ∉ {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ₀ (ω i)} ∧
            ω ∉ {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n g) (ω i)} ∧
            ω ∉ {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n h) (ω i)} ∧
            ω ∉ {ω : Fin n → 𝓧 | c ≤ |bvmLogRatio M f θ₀ J sc n g h ω|} :=
          ⟨hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2⟩
        simp only [Set.mem_setOf_eq, not_not] at hc0 hcg hch
        simp only [Set.mem_setOf_eq, not_le] at hclr
        have hexp : ρ n ω
            = ENNReal.ofReal (Real.exp (bvmLogRatio M f θ₀ J sc n g h ω)) :=
          bvmPairRatio_eq_exp_bvmLogRatio hfg hfh hc0 hcg hch
        have hle1 : ENNReal.ofReal ε₀ ≤ 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hε₀1.le
        have hlt : ρ n ω < 1 - ENNReal.ofReal ε₀ := by
          by_contra hge
          rw [not_lt] at hge
          have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ε₀ + ρ n ω := by
            calc (1 : ℝ≥0∞) = ENNReal.ofReal ε₀ + (1 - ENNReal.ofReal ε₀) :=
                  (add_tsub_cancel_of_le hle1).symm
              _ ≤ ENNReal.ofReal ε₀ + ρ n ω := add_le_add le_rfl hge
          have hmono : (1 : ℝ≥0∞) - ρ n ω ≤ ENNReal.ofReal ε₀ := tsub_le_iff_right.mpr h1
          exact absurd (lt_of_lt_of_le hω hmono) (lt_irrefl _)
        rw [hexp, show (1 : ℝ≥0∞) - ENNReal.ofReal ε₀ = ENNReal.ofReal (1 - ε₀) by
          rw [ENNReal.ofReal_sub _ hε₀.le, ENNReal.ofReal_one]] at hlt
        have hlt' : Real.exp (bvmLogRatio M f θ₀ J sc n g h ω) < 1 - ε₀ :=
          (ENNReal.ofReal_lt_ofReal_iff h1ε).mp hlt
        have hlog : bvmLogRatio M f θ₀ J sc n g h ω < Real.log (1 - ε₀) :=
          (Real.lt_log_iff_exp_lt h1ε).mpr hlt'
        have : c ≤ |bvmLogRatio M f θ₀ J sc n g h ω| := by
          rw [hcdef]
          refine le_trans (le_of_eq rfl) ?_
          rw [abs_of_neg (by linarith [Real.log_neg h1ε (by linarith : 1 - ε₀ < 1)])]
          linarith
        exact absurd this (not_le.mpr hclr)
      calc ∫⁻ ω, (1 - ρ n ω) ∂(productMeasure M μ (bvmLocalUnscale θ₀ n h) n)
          ≤ ENNReal.ofReal ε₀ + productMeasure M μ (bvmLocalUnscale θ₀ n h) n
              {ω : Fin n → 𝓧 | ENNReal.ofReal ε₀ < 1 - ρ n ω} :=
            lintegral_le_add_measure_gt _ (hYmeas n) (fun ω => tsub_le_self) _
        _ ≤ ENNReal.ofReal ε₀ + (productMeasure M μ (bvmLocalUnscale θ₀ n h) n
                {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density θ₀ (ω i)}
              + (productMeasure M μ (bvmLocalUnscale θ₀ n h) n
                  {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n g) (ω i)}
                + (productMeasure M μ (bvmLocalUnscale θ₀ n h) n
                    {ω : Fin n → 𝓧 | ¬ ∀ i, 0 < M.density (bvmLocalUnscale θ₀ n h) (ω i)}
                  + productMeasure M μ (bvmLocalUnscale θ₀ n h) n
                      {ω : Fin n → 𝓧 | c ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}))) := by
            refine add_le_add le_rfl (le_trans (measure_mono hincl) ?_)
            refine le_trans (measure_union_le _ _) (add_le_add le_rfl ?_)
            exact le_trans (measure_union_le _ _) (add_le_add le_rfl (measure_union_le _ _))
        _ ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ := add_le_add le_rfl hn
        _ = ENNReal.ofReal (2 * ε₀) := by
            rw [two_mul, ENNReal.ofReal_add hε₀.le hε₀.le]
    refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
    rcases eq_or_ne ε ∞ with rfl | hεT
    · exact Eventually.of_forall fun n => le_top
    · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεT
      refine (hlim (min (1 / 2) (ε.toReal / 4)) (lt_min (by norm_num) (by linarith))
        (lt_of_le_of_lt (min_le_left _ _) (by norm_num))).mono fun n hn => ?_
      refine le_trans hn ?_
      have hle : 2 * min (1 / 2 : ℝ) (ε.toReal / 4) ≤ ε.toReal := by
        have := min_le_right (1 / 2 : ℝ) (ε.toReal / 4)
        linarith
      calc ENNReal.ofReal (2 * min (1 / 2 : ℝ) (ε.toReal / 4))
          ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hle
        _ = ε := ENNReal.ofReal_toReal hεT
  have := ENNReal.Tendsto.mul hfpre (Or.inr (by simp)) hmain (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at this
  exact this.congr fun n => (hident n).symm

-- LEAN-ONLY: joint measurability of the pair defect in `(ω, (h, g))`.
private lemma measurable_bvmPairDefect_pair
    (hM_joint : Measurable (Function.uncurry M.density)) (hf : Measurable f)
    (J : Matrix (Fin k) (Fin k) ℝ) {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc)
    (n : ℕ) :
    Measurable fun q : (Fin n → 𝓧) × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) =>
      bvmPairDefect M f θ₀ J sc n q.2.1 q.2.2 q.1 := by
  have hsh := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun q : (Fin n → 𝓧) × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) => q.2.1)
    (b := fun q => q.1) measurable_snd.fst measurable_fst
  have hsg := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun q : (Fin n → 𝓧) × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) => q.2.2)
    (b := fun q => q.1) measurable_snd.snd measurable_fst
  have hth := measurable_bvmGaussDens_comp J hsc n
    (a := fun q : (Fin n → 𝓧) × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) => q.2.1)
    (b := fun q => q.1) measurable_snd.fst measurable_fst
  have htg := measurable_bvmGaussDens_comp J hsc n
    (a := fun q : (Fin n → 𝓧) × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) => q.2.2)
    (b := fun q => q.1) measurable_snd.snd measurable_fst
  unfold bvmPairDefect
  exact ((hsh.mul htg).sub (hsg.mul hth)).div htg

private lemma measurable_bvmPairDefect_pair'
    (hM_joint : Measurable (Function.uncurry M.density)) (hf : Measurable f)
    (J : Matrix (Fin k) (Fin k) ℝ) {sc : 𝓧 → EuclideanSpace ℝ (Fin k)} (hsc : Measurable sc)
    (n : ℕ) (ω : Fin n → 𝓧) :
    Measurable fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      bvmPairDefect M f θ₀ J sc n p.1 p.2 ω := by
  have hsh := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) => p.1)
    (b := fun _ => ω) measurable_fst measurable_const
  have hsg := measurable_bvmJointDens_comp (M := M) (θ₀ := θ₀) hM_joint hf n
    (a := fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) => p.2)
    (b := fun _ => ω) measurable_snd measurable_const
  have hth := measurable_bvmGaussDens_comp J hsc n
    (a := fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) => p.1)
    (b := fun _ => ω) measurable_fst measurable_const
  have htg := measurable_bvmGaussDens_comp J hsc n
    (a := fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) => p.2)
    (b := fun _ => ω) measurable_snd measurable_const
  unfold bvmPairDefect
  exact ((hsh.mul htg).sub (hsg.mul hth)).div htg

/-- **The Step-B majorant vanishes in mixture mean** (vdV p. 143, last display): Fubini turns
the `μⁿ`-mean of the (unnormalized) Step-B majorant into a double Lebesgue integral of the
fixed-pair defects, which vanishes by dominated convergence. -/
private lemma lintegral_bvmStepBBound_mul_tendsto
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {R u : ℝ}
    -- LEAN-ONLY: nontrivial localization radius, inner ball inside the outer one
    (hR : 0 < R) (hu : u ≤ R) :
    Tendsto (fun n => ∫⁻ ω, bvmStepBBound M f θ₀ J sc n R ω
        * bvmNumer M f θ₀ n (Metric.ball 0 u) ω ∂(Measure.pi fun _ : Fin n => μ))
      atTop (𝓝 0) := by
  classical
  set C : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall 0 R with hCdef
  set lamC : Measure (EuclideanSpace ℝ (Fin k)) := volume.restrict C with hlamC
  have hCmeas : MeasurableSet C := measurableSet_closedBall
  have hVfin : lamC Set.univ ≠ ∞ := by
    rw [hlamC, Measure.restrict_apply_univ]
    exact measure_closedBall_lt_top.ne
  haveI : IsFiniteMeasure lamC := ⟨lt_of_le_of_ne le_top hVfin⟩
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) u ⊆ C :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hu)
  -- Step 1: bound the integrand by the unnormalized double integral.
  have hstep1 : ∀ (n : ℕ) (ω : Fin n → 𝓧),
      bvmStepBBound M f θ₀ J sc n R ω * bvmNumer M f θ₀ n (Metric.ball 0 u) ω
        ≤ ∫⁻ h in C, ∫⁻ g in C, bvmPairDefect M f θ₀ J sc n h g ω ∂volume ∂volume := by
    intro n ω
    have hmono : bvmNumer M f θ₀ n (Metric.ball 0 u) ω ≤ bvmNumer M f θ₀ n C ω :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    calc bvmStepBBound M f θ₀ J sc n R ω * bvmNumer M f θ₀ n (Metric.ball 0 u) ω
        ≤ bvmStepBBound M f θ₀ J sc n R ω * bvmNumer M f θ₀ n C ω :=
          mul_le_mul_right hmono _
      _ ≤ ∫⁻ h in C, ∫⁻ g in C, bvmPairDefect M f θ₀ J sc n h g ω ∂volume ∂volume :=
          ennreal_inv_mul_mul_le _ _
  -- Step 2: Fubini.
  have hstep2 : ∀ n : ℕ,
      ∫⁻ ω, (∫⁻ h in C, ∫⁻ g in C, bvmPairDefect M f θ₀ J sc n h g ω ∂volume ∂volume)
          ∂(Measure.pi fun _ : Fin n => μ)
        = ∫⁻ p, (∫⁻ ω, bvmPairDefect M f θ₀ J sc n p.1 p.2 ω
            ∂(Measure.pi fun _ : Fin n => μ)) ∂(lamC.prod lamC) := by
    intro n
    have hjoint := measurable_bvmPairDefect_pair (M := M) (θ₀ := θ₀) hM_joint
      hπ.measurable J hsc n
    have hinner : ∀ ω : Fin n → 𝓧,
        (∫⁻ h in C, ∫⁻ g in C, bvmPairDefect M f θ₀ J sc n h g ω ∂volume ∂volume)
          = ∫⁻ p, bvmPairDefect M f θ₀ J sc n p.1 p.2 ω ∂(lamC.prod lamC) := by
      intro ω
      rw [lintegral_prod _
        (measurable_bvmPairDefect_pair' (M := M) (θ₀ := θ₀) hM_joint hπ.measurable
          J hsc n ω).aemeasurable]
    simp_rw [hinner]
    refine lintegral_lintegral_swap ?_
    unfold Function.uncurry
    exact hjoint.aemeasurable
  -- Step 3: dominated convergence for the double Lebesgue integral.
  have hdct : Tendsto (fun n : ℕ => ∫⁻ p, (∫⁻ ω, bvmPairDefect M f θ₀ J sc n p.1 p.2 ω
      ∂(Measure.pi fun _ : Fin n => μ)) ∂(lamC.prod lamC)) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ p ∂(lamC.prod lamC),
        (∫⁻ ω, bvmPairDefect M f θ₀ J sc n p.1 p.2 ω ∂(Measure.pi fun _ : Fin n => μ))
          ≤ ENNReal.ofReal (f θ₀ + 1) := by
      have hcont : ∀ᶠ θ in 𝓝 θ₀, f θ < f θ₀ + 1 :=
        hπ.continuousAt.eventually (Iio_mem_nhds (lt_add_one (f θ₀)))
      obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.mp hcont
      have hshrink : Tendsto (fun n : ℕ => R / Real.sqrt n) atTop (𝓝 0) := by
        have hsq : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        simpa [div_eq_mul_inv] using hsq.const_mul R
      filter_upwards [hshrink.eventually (Iio_mem_nhds hδ), eventually_gt_atTop 0]
        with n hn hn0
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
      rw [hlamC, Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (hCmeas.prod hCmeas) fun p hp => ?_
      have hp1 : ‖p.1‖ ≤ R := by
        have := hp.1
        rwa [hCdef, Metric.mem_closedBall, dist_zero_right] at this
      have hdist : dist (bvmLocalUnscale θ₀ n p.1) θ₀ < δ := by
        rw [bvmLocalUnscale, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hsqrt), inv_mul_eq_div]
        refine lt_of_le_of_lt (div_le_div_of_nonneg_right hp1 hsqrt.le) ?_
        exact Set.mem_Iio.mp hn
      refine le_trans (lintegral_bvmPairDefect_le hPDF hκ hM_joint p.1 p.2) ?_
      exact ENNReal.ofReal_le_ofReal (le_of_lt (hδf hdist))
    have hmeas : ∀ᶠ n : ℕ in atTop, Measurable (fun p :
        EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        ∫⁻ ω, bvmPairDefect M f θ₀ J sc n p.1 p.2 ω ∂(Measure.pi fun _ : Fin n => μ)) := by
      refine Filter.Eventually.of_forall fun n => ?_
      have hjoint := measurable_bvmPairDefect_pair (M := M) (θ₀ := θ₀) hM_joint
        hπ.measurable J hsc n
      exact hjoint.lintegral_prod_left' (μ := (Measure.pi fun _ : Fin n => μ))
    have hlim : ∀ᵐ p ∂(lamC.prod lamC), Tendsto (fun n : ℕ =>
        ∫⁻ ω, bvmPairDefect M f θ₀ J sc n p.1 p.2 ω ∂(Measure.pi fun _ : Fin n => μ))
        atTop (𝓝 0) :=
      Filter.Eventually.of_forall fun p =>
        lintegral_bvmPairDefect_tendsto hPDF hsc hDQM hJ_pd hJ hκ hM_joint hπ p.2 p.1
    have hfin : ∫⁻ _, ENNReal.ofReal (f θ₀ + 1) ∂(lamC.prod lamC) ≠ ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have := tendsto_lintegral_filter_of_dominated_convergence
      (fun _ => ENNReal.ofReal (f θ₀ + 1)) hmeas hbound hfin hlim
    simpa using this
  have hle : ∀ n : ℕ, ∫⁻ ω, bvmStepBBound M f θ₀ J sc n R ω
      * bvmNumer M f θ₀ n (Metric.ball 0 u) ω ∂(Measure.pi fun _ : Fin n => μ)
      ≤ ∫⁻ p, (∫⁻ ω, bvmPairDefect M f θ₀ J sc n p.1 p.2 ω
          ∂(Measure.pi fun _ : Fin n => μ)) ∂(lamC.prod lamC) := by
    intro n
    rw [← hstep2 n]
    exact lintegral_mono (hstep1 n)
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
  exact ((ENNReal.tendsto_nhds_zero.mp hdct) ε hε).mono fun n hn => le_trans (hle n) hn

-- LEAN-ONLY: uniform tightness of the score sums (score CLT + Prohorov's converse).
private lemma exists_scoreSum_bound
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      productMeasure M μ θ₀ n {ω : Fin n → 𝓧 | K < ‖scoreSum sc n ω‖} ≤ ε := by
  classical
  haveI hProb : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF θ₀ n
  have hscmeas : ∀ n : ℕ, Measurable (scoreSum sc n) := by
    intro n
    have hsum : Measurable fun ω : Fin n → 𝓧 => ∑ i, sc (ω i) :=
      Finset.measurable_sum Finset.univ fun i _ => hsc.comp (measurable_pi_apply i)
    unfold scoreSum
    exact hsum.const_smul ((Real.sqrt (n : ℝ))⁻¹)
  haveI hmapProb : ∀ n : ℕ,
      IsProbabilityMeasure ((productMeasure M μ θ₀ n).map (scoreSum sc n)) := fun n => ⟨by
    rw [Measure.map_apply (hscmeas n) MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  haveI hGprob : IsProbabilityMeasure
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) := inferInstance
  have hwc := AsymptoticStatistics.AsymptoticRepresentation.scoreSum_weakly_converges
    M μ θ₀ sc hsc (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀)
    (fun _ _ => hPDF.density_integral_eq_one _) (fun _ _ => hPDF.density_integrable _)
    hDQM J hJ_pd.posSemidef hJ
  have htight := AsymptoticStatistics.Prohorov.weakConverges_range_tight
    (fun n => (productMeasure M μ θ₀ n).map (scoreSum sc n)) _ hwc
  obtain ⟨Kc, hKc, hKle⟩ :=
    MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight ε hε
  obtain ⟨r, hr⟩ := hKc.isBounded.subset_closedBall 0
  refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun n => ?_⟩
  have hsub : {x : EuclideanSpace ℝ (Fin k) | max r 1 < ‖x‖} ⊆ Kcᶜ := by
    intro x hx hxK
    have hx' := hr hxK
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    exact absurd (lt_of_le_of_lt (le_max_left r 1) hx) (not_lt.mpr hx')
  calc productMeasure M μ θ₀ n {ω : Fin n → 𝓧 | max r 1 < ‖scoreSum sc n ω‖}
      = ((productMeasure M μ θ₀ n).map (scoreSum sc n))
          {x : EuclideanSpace ℝ (Fin k) | max r 1 < ‖x‖} := by
        rw [Measure.map_apply (hscmeas n) (measurableSet_lt measurable_const measurable_norm),
          Set.preimage_setOf_eq]
    _ ≤ ((productMeasure M μ θ₀ n).map (scoreSum sc n)) Kcᶜ := measure_mono hsub
    _ ≤ ε := hKle _ ⟨n, rfl⟩

-- LEAN-ONLY: the local mass is finite predictive-a.e., and where it vanishes the conditioned
-- posterior is the zero measure (so the conditioned total-variation distance vanishes too).
private lemma bvmNumer_ne_top_and_tvDist_zero_ae
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {R : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hR : 0 < R)
    -- LEAN-ONLY: the rescaled ball sits inside the absolute-continuity zone
    {n : ℕ} (hn : R < r₀ * Real.sqrt n) :
    ∀ᵐ ω ∂(iidKernel κ n ∘ₘ π),
      bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω ≠ ∞ ∧
        (bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω = 0 →
          Minimaxity.tvDist
            ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin k)) R])
            ((bvmGaussian J sc n ω)[|Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin k)) R]) = 0) := by
  classical
  have hsqrt : 0 < Real.sqrt n := by
    rcases le_or_gt (Real.sqrt n) 0 with hle | hlt
    · exact absurd hn (by nlinarith [hπ.rad_pos])
    · exact hlt
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · subst h0; simp at hsqrt
    · exact h1
  set C : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall 0 R with hCdef
  have hC : MeasurableSet C := measurableSet_closedBall
  have hsubC : bvmLocalScale θ₀ n ⁻¹' C ⊆ Metric.ball θ₀ r₀ := by
    intro θ hθ
    have h1 : bvmLocalScale θ₀ n θ ∈ C := hθ
    rw [hCdef, Metric.mem_closedBall, dist_zero_right, bvmLocalScale, norm_smul,
      Real.norm_eq_abs, abs_of_pos hsqrt] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : Real.sqrt n * ‖θ - θ₀‖ < Real.sqrt n * r₀ :=
      lt_of_le_of_lt h1 (by rw [mul_comm]; exact hn)
    exact lt_of_mul_lt_mul_left h2 hsqrt.le
  have hdens_meas : Measurable
      (Function.uncurry fun θ (x : 𝓧) => ENNReal.ofReal (M.density θ x)) :=
    ENNReal.measurable_ofReal.comp hM_joint
  have hP : Measurable (Function.uncurry
      fun (θ : EuclideanSpace ℝ (Fin k)) (x : Fin n → 𝓧) =>
        ∏ i, ENNReal.ofReal (M.density θ (x i))) :=
    measurable_uncurry_prod_likelihood hdens_meas
  have hκ' : ∀ θ, iidKernel κ n θ
      = (Measure.pi fun _ : Fin n => μ).withDensity
          fun x => ∏ i, ENNReal.ofReal (M.density θ (x i)) :=
    fun θ => iidKernel_withDensity hdens_meas hκ n θ
  have hpreC : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' C) := (measurable_bvmLocalScale θ₀ n) hC
  have hqpos : (0 : ℝ) < ((Real.sqrt n)⁻¹) ^ k := by positivity
  have hq : ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  filter_upwards [posterior_apply_eq_div (π := π) hP hκ' (MeasurableSet.univ
      (α := EuclideanSpace ℝ (Fin k))),
    posterior_apply_eq_div (π := π) hP hκ' hpreC] with ω hωU hωC
  set Z := ∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π with hZdef
  have hZ1 : Z / Z = 1 := by
    have h := hωU
    simp only [Measure.restrict_univ, measure_univ] at h
    exact h.symm
  have hZtop : Z ≠ ∞ := by intro h0; rw [h0] at hZ1; simp at hZ1
  have hjac := lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 hC hsubC ω
  have hle : ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) * bvmNumer M f θ₀ n C ω ≤ Z := by
    rw [← hjac]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have h1 : bvmNumer M f θ₀ n C ω ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.mul_top hq] at hle
    exact hZtop (top_le_iff.mp hle)
  refine ⟨h1, fun hS0 => ?_⟩
  have hpost : bvmLocalPosterior κ π θ₀ n ω C = 0 := by
    rw [bvmLocalPosterior, Kernel.map_apply' _ (measurable_bvmLocalScale θ₀ n) _ hC, hωC,
      hjac, hS0, mul_zero, ENNReal.zero_div]
  have hcond : ((bvmLocalPosterior κ π θ₀ n ω)[|C]) = 0 := by
    rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.mpr hpost, smul_zero]
  rw [hcond]
  refine le_antisymm (iSup_le fun t => iSup_le fun _ => ?_) (zero_le)
  simp

/-- **Step B: the conditioned Bernstein–von Mises convergence** (vdV pp. 142–143). For every
fixed radius `R > 0` and every `δ > 0`, the `P^n_{θ₀}`-probability that the conditioned
local posterior and the conditioned Gaussian differ by at least `δ` in total variation tends
to zero. -/
theorem local_tv_tendsto
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of the Bernstein–von Mises theorem; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {R : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hR : 0 < R) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ Minimaxity.tvDist
            ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall 0 R])
            ((bvmGaussian J sc n ω)[|Metric.closedBall 0 R])})
        atTop (𝓝 0) := by
  classical
  intro δ hδ
  have hδ'0 : (0 : ℝ≥0∞) < min δ 1 := lt_min hδ zero_lt_one
  have hδ'T : min δ 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hV0 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) ≠ 0 :=
    (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 hR)
      (measure_mono Metric.ball_subset_closedBall)).ne'
  have hRn : ∀ᶠ n : ℕ in atTop, R < r₀ * Real.sqrt n := by
    have hgo : Tendsto (fun n : ℕ => r₀ * Real.sqrt n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hπ.rad_pos
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    exact hgo.eventually_gt_atTop R
  have hWmeas : ∀ n : ℕ, Measurable (bvmStepBBound M f θ₀ J sc n R) := fun n =>
    measurable_bvmStepBBound (M := M) (θ₀ := θ₀) hM_joint hπ.measurable J hsc n R
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨K, hK0, hKbd⟩ := exists_scoreSum_bound hPDF hsc hDQM hJ_pd hJ hε2
  obtain ⟨cK, hcKT, hcKeq⟩ : ∃ c : ℝ≥0∞, c ≠ ∞ ∧
      ENNReal.ofReal (Real.exp
          (2 * (R * K + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * R ^ 2)))
        / volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R) = c :=
    ⟨_, ENNReal.div_ne_top ENNReal.ofReal_ne_top hV0, rfl⟩
  -- the measurable exceptional events
  have hex : ∀ n : ℕ, ∃ Nset : Set (Fin n → 𝓧), MeasurableSet Nset ∧
      (iidKernel κ n ∘ₘ π) Nset = 0 ∧
      ∀ ω, ω ∉ Nset → R < r₀ * Real.sqrt n →
        (bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω ≠ ∞ ∧
          (bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω = 0 →
            Minimaxity.tvDist
              ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin k)) R])
              ((bvmGaussian J sc n ω)[|Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin k)) R]) = 0) ∧
          (bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω ≠ 0 →
            bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω ≠ ∞ →
            ‖scoreSum sc n ω‖ ≤ K →
            Minimaxity.tvDist
                ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall
                  (0 : EuclideanSpace ℝ (Fin k)) R])
                ((bvmGaussian J sc n ω)[|Metric.closedBall
                  (0 : EuclideanSpace ℝ (Fin k)) R])
              ≤ cK * bvmStepBBound M f θ₀ J sc n R ω)) := by
    intro n
    by_cases hn : R < r₀ * Real.sqrt n
    · have hae := (bvmNumer_ne_top_and_tvDist_zero_ae (J := J) (sc := sc) hκ hM_joint
        hπ hR hn).and (tvDist_cond_le_bvmStepBBound (K := K) (sc := sc) hκ hM_joint hπ
        hJ_pd hR hn)
      obtain ⟨t, hts, htm, htz⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
      refine ⟨t, htm, htz, fun ω hω _ => ?_⟩
      have hgood := not_not.mp (mt (@hts ω) hω)
      exact ⟨hgood.1.1, hgood.1.2, hcKeq ▸ hgood.2⟩
    · exact ⟨∅, MeasurableSet.empty, measure_empty, fun ω _ hcon => absurd hcon hn⟩
  choose N hNmeas hNzero hNprop using hex
  -- the Markov/mixture bound on the majorant event
  have hWset : ∀ n : ℕ, MeasurableSet {ω : Fin n → 𝓧 |
      min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω} := fun n =>
    measurableSet_le measurable_const (measurable_const.mul (hWmeas n))
  have hI : Tendsto (fun n : ℕ => ∫⁻ ω, bvmStepBBound M f θ₀ J sc n R ω
      * bvmNumer M f θ₀ n (Metric.ball 0 R) ω ∂(Measure.pi fun _ : Fin n => μ))
      atTop (𝓝 0) :=
    lintegral_bvmStepBBound_mul_tendsto hPDF hsc hDQM hJ_pd hJ hκ hM_joint hπ hR le_rfl
  obtain ⟨c₀, hc₀pos, hc₀ev⟩ := prior_ball_inv_sqrt_lower (π := π) hπ (u := R) hR
  have hAT : cK * c₀⁻¹ / min δ 1 ≠ ∞ := by
    refine ENNReal.div_ne_top (ENNReal.mul_ne_top hcKT ?_) hδ'0.ne'
    exact ENNReal.inv_ne_top.mpr hc₀pos.ne'
  have hmix : Tendsto (fun n : ℕ => bvmMixture κ π θ₀ R n
      {ω : Fin n → 𝓧 | min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω}) atTop (𝓝 0) := by
    have hlin : Tendsto (fun n : ℕ => (cK * c₀⁻¹ / min δ 1)
        * ∫⁻ ω, bvmStepBBound M f θ₀ J sc n R ω
            * bvmNumer M f θ₀ n (Metric.ball 0 R) ω ∂(Measure.pi fun _ : Fin n => μ))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hI (Or.inr hAT)
    have hbnd : ∀ᶠ n : ℕ in atTop, bvmMixture κ π θ₀ R n
        {ω : Fin n → 𝓧 | min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω}
        ≤ (cK * c₀⁻¹ / min δ 1) * ∫⁻ ω, bvmStepBBound M f θ₀ J sc n R ω
            * bvmNumer M f θ₀ n (Metric.ball 0 R) ω ∂(Measure.pi fun _ : Fin n => μ) := by
      filter_upwards [hc₀ev, eventually_ge_atTop 1, hRn] with n hc₀n hn1 hn
      have hqpos : (0 : ℝ) < ((Real.sqrt n)⁻¹) ^ k := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
        have : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
        positivity
      have hq0 : ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hqpos).ne'
      have hqT : ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) ≠ ∞ := ENNReal.ofReal_ne_top
      have hratio : (π (Metric.ball θ₀ (R / Real.sqrt n)))⁻¹
          * ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) ≤ c₀⁻¹ := by
        calc (π (Metric.ball θ₀ (R / Real.sqrt n)))⁻¹
              * ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k)
            ≤ (c₀ * ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k))⁻¹
                * ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) :=
              mul_le_mul_left (ENNReal.inv_le_inv.mpr hc₀n) _
          _ = c₀⁻¹ := by
              rw [ENNReal.mul_inv (Or.inl hc₀pos.ne') (Or.inr hq0), mul_assoc,
                ENNReal.inv_mul_cancel hq0 hqT, mul_one]
      have hmk := meas_ge_le_lintegral_div
        (μ := bvmMixture κ π θ₀ R n)
        (f := fun ω : Fin n → 𝓧 => cK * bvmStepBBound M f θ₀ J sc n R ω)
        (measurable_const.mul (hWmeas n)).aemeasurable hδ'0.ne' hδ'T
      refine le_trans hmk ?_
      rw [lintegral_const_mul' _ _ hcKT,
        lintegral_bvmMixture_eq hκ hM_joint hπ hn1 hn (hWmeas n)]
      rw [ENNReal.div_le_iff_le_mul (Or.inl hδ'0.ne') (Or.inl hδ'T)]
      set Iv : ℝ≥0∞ := ∫⁻ ω, bvmStepBBound M f θ₀ J sc n R ω
          * bvmNumer M f θ₀ n (Metric.ball 0 R) ω ∂(Measure.pi fun _ : Fin n => μ) with hIv
      calc cK * ((π (Metric.ball θ₀ (R / Real.sqrt n)))⁻¹
              * ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) * Iv)
          ≤ cK * (c₀⁻¹ * Iv) := mul_le_mul_right (mul_le_mul_left hratio _) _
        _ = cK * c₀⁻¹ / min δ 1 * Iv * min δ 1 := by
            rw [div_eq_mul_inv,
              show cK * c₀⁻¹ * (min δ 1)⁻¹ * Iv * min δ 1
                = (min δ 1)⁻¹ * min δ 1 * (cK * (c₀⁻¹ * Iv)) from by ring,
              ENNReal.inv_mul_cancel hδ'0.ne' hδ'T, one_mul]
    refine ENNReal.tendsto_nhds_zero.mpr fun ε' hε' => ?_
    filter_upwards [hbnd, (ENNReal.tendsto_nhds_zero.mp hlin) ε' hε'] with n h1 h2
    exact le_trans h1 h2
  have hWtend : Tendsto (fun n : ℕ => productMeasure M μ θ₀ n
      {ω : Fin n → 𝓧 | min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω}) atTop (𝓝 0) :=
    (mutuallyContiguous_mixture_base hPDF hsc hDQM hJ_pd hJ hκ hπ hR).2 _ hWset hmix
  have hNtend : Tendsto (fun n : ℕ => productMeasure M μ θ₀ n (N n)) atTop (𝓝 0) :=
    measure_tendsto_zero_of_predictive_null hPDF hsc hDQM hJ_pd hJ hκ hπ hNmeas hNzero
  have hsum : Tendsto (fun n : ℕ => productMeasure M μ θ₀ n (N n)
      + productMeasure M μ θ₀ n
          {ω : Fin n → 𝓧 | min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω})
      atTop (𝓝 0) := by simpa using hNtend.add hWtend
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hsum) (ε / 2) hε2, hRn] with n hn hRn'
  have hincl : {ω : Fin n → 𝓧 | δ ≤ Minimaxity.tvDist
        ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall 0 R])
        ((bvmGaussian J sc n ω)[|Metric.closedBall 0 R])}
      ⊆ {ω : Fin n → 𝓧 | K < ‖scoreSum sc n ω‖}
        ∪ (N n ∪ {ω : Fin n → 𝓧 |
            min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω}) := by
    intro ω hω
    by_cases hT : K < ‖scoreSum sc n ω‖
    · exact Or.inl hT
    by_cases hN : ω ∈ N n
    · exact Or.inr (Or.inl hN)
    obtain ⟨h1, h2, h3⟩ := hNprop n ω hN hRn'
    by_cases hS0 : bvmNumer M f θ₀ n (Metric.closedBall 0 R) ω = 0
    · exact absurd (le_trans hω (le_of_eq (h2 hS0))) (by simpa using hδ.ne')
    · refine Or.inr (Or.inr ?_)
      exact le_trans (min_le_left _ _) (le_trans hω (h3 hS0 h1 (not_lt.mp hT)))
  calc productMeasure M μ θ₀ n {ω : Fin n → 𝓧 | δ ≤ Minimaxity.tvDist
        ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall 0 R])
        ((bvmGaussian J sc n ω)[|Metric.closedBall 0 R])}
      ≤ productMeasure M μ θ₀ n ({ω : Fin n → 𝓧 | K < ‖scoreSum sc n ω‖}
          ∪ (N n ∪ {ω : Fin n → 𝓧 |
              min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω})) := measure_mono hincl
    _ ≤ productMeasure M μ θ₀ n {ω : Fin n → 𝓧 | K < ‖scoreSum sc n ω‖}
          + (productMeasure M μ θ₀ n (N n) + productMeasure M μ θ₀ n
              {ω : Fin n → 𝓧 | min δ 1 ≤ cK * bvmStepBBound M f θ₀ J sc n R ω}) :=
        le_trans (measure_union_le _ _) (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ε / 2 + ε / 2 := add_le_add (hKbd n) hn
    _ = ε := ENNReal.add_halves ε

end StatLean.Bayesian
